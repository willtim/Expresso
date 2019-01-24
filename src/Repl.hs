{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Main
-- Copyright   : (c) Tim Williams 2017-2019
-- License     : BSD3
--
-- Maintainer  : info@timphilipwilliams.com
-- Stability   : experimental
-- Portability : portable
--
-- Expresso Read-Eval-Print-Loop.
--
module Main where

import Control.Applicative
import Control.Monad (forM_)
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Char
import Data.Version
import System.Console.Haskeline (InputT)
import System.Console.Haskeline.MonadException ()
import System.Directory
import System.FilePath
import Text.Parsec.String (Parser)
import qualified System.Console.Haskeline as HL
import qualified Text.Parsec as P

import Expresso
import Expresso.Parser ( pExp, pLetDecl, pSynonymDecl, topLevel
                       , reserved, reservedOp, stringLiteral
                       )
import Expresso.Utils

import Paths_expresso

ps1 :: String
ps1 = "λ"

data Mode = SingleLine | MultiLine | Quitting

data ReplState = ReplState
  { stateMode    :: Mode
  , stateBuffer  :: [String]
  , stateEnv     :: Environments
  , stateLibDirs :: [FilePath]
  }

data Command
  = Peek      ExpI
  | Type      ExpI
  | Load      FilePath
  | ChangeCWD FilePath
  | BeginMulti
  | Reset
  | DumpEnv
  | Quit
  | Help

data Line
  = Command Command
  | Term ExpI
  | Decl (Bind Name) (Maybe Type) ExpI
  | TypeDecl SynonymDecl
  | NoOp

type Repl = InputT (StateT ReplState IO)

main :: IO ()
main = do
  preludePath <- liftIO $ getDataFileName "Prelude.x"
  currentDir  <- liftIO getCurrentDirectory
  let libDirs = [takeDirectory preludePath, currentDir]
  runRepl libDirs $ do
    mapM_ spew
      [ unwords ["Expresso", showVersion version, "REPL"]
      , "Type :help or :h for a list of commands"
      ]
    HL.catch
        (loadPrelude preludePath)
        (\(e :: HL.SomeException) ->
             spew $ "Warning: Couldn't open " ++ preludePath ++ ": " ++ show e)
    repl

-- | The read-eval-print-loop
repl :: Repl ()
repl = step repl
       `HL.catch` (\(e :: HL.SomeException) -> spew (show e) >> repl)
  where
    step :: Repl () -> Repl ()
    step cont = HL.withInterrupt $ do
      mode <- lift $ gets stateMode
      case mode of
        MultiLine  -> do
          minput <- HL.getInputLine $ ps1 ++ "| "
          whenJust minput $ \input ->
              if isEndMulti input
                then doEndMulti
                else lift $ modify (addToBuffer input)
          cont
        SingleLine -> do
          minput <- HL.getInputLine $ ps1 ++ "> "
          whenJust minput process
          cont
        Quitting   -> do
          spew "Goodbye."
          return ()

process :: String -> Repl ()
process str = do
  case parseLine str of
    Left err              -> spew err
    Right (Command c)     -> doCommand c
    Right (Term e)        -> doEval showValue' e
    Right (Decl b mty e)  -> doDecl b mty e
    Right (TypeDecl syn)  -> doTypeDecl syn
    Right NoOp            -> return ()
 `HL.catch` handler
  where
    handler :: HL.SomeException -> Repl ()
    handler ex = spew $ "Caught exception: " ++ show ex

runRepl :: [FilePath] -> Repl a -> IO a
runRepl libDirs m = do
    historyFile <- (</> ".expresso_history") <$> getHomeDirectory
    let settings = HL.defaultSettings {HL.historyFile = Just historyFile}
    evalStateT (HL.runInputT settings m) (emptyReplState libDirs)

emptyReplState :: [FilePath] -> ReplState
emptyReplState libDirs = ReplState
  { stateMode    = SingleLine
  , stateBuffer  = mempty
  , stateEnv     = setLibDirs libDirs initEnvironments
  , stateLibDirs = libDirs
  }

loadPrelude :: FilePath -> Repl ()
loadPrelude path = do
  spew $ "Loading Prelude from " ++ path
  doLoad path

doCommand :: Command -> Repl ()
doCommand c = case c of
  Peek e         -> doEval (return . showValue) e
  Type e         -> doTypeOf e
  Load path      -> doLoad path
  ChangeCWD path -> liftIO $ setCurrentDirectory path
  Quit           -> lift $ modify (setMode Quitting)
  BeginMulti     -> lift $ modify (setMode MultiLine)
  Reset          -> doReset
  DumpEnv        -> doDumpEnv
  Help           -> mapM_ spew
    [ "REPL commands available from the prompt:"
    , ""
    , "<expression>                evaluate an expression"
    , ":peek <expression>          evaluate, but not deeply"
    , ":load <filename>            import record expression as a module"
    , ":{\\n ..lines.. \\n:}\\n       multiline command"
    , ":cd <path>                  change current working directory"
    , ":type <term>                show the type of <term>"
    , ":reset                      reset REPL, unloading all definitions"
    , ":env                        dump bound symbols in the environment"
    , ":quit                       exit REPL"
    , ":help                       display this list of commands"
    , ""
    ]

doEval :: (Value -> IO String) -> ExpI -> Repl ()
doEval pp e = do
  envs <- lift $ gets stateEnv
  v'e  <- liftIO $ evalWithEnv envs e
  case v'e of
      Left err  -> spew err
      Right val -> liftIO (pp val) >>= spew

doLoad :: FilePath -> Repl ()
doLoad path =
  doDecl RecWildcard Nothing
       $ Fix (InR (K (Import path)) :*: K dummyPos)

doDecl :: Bind Name -> Maybe Type -> ExpI -> Repl ()
doDecl b mty e = do
  envs   <- lift $ gets stateEnv
  envs'e <- liftIO $ runEvalM $ bind envs b mty e
  case envs'e of
      Left err    -> spew err
      Right envs' -> lift $ modify (setEnv envs')

doTypeDecl :: SynonymDecl -> Repl ()
doTypeDecl syn = do
  envs <- lift $ gets stateEnv
  let envs'e = runExcept
             . installSynonyms [syn]
             . uninstallSynonym syn
             $ envs
  case envs'e of
      Left err    -> spew err
      Right envs' -> lift $ modify (setEnv envs')

doTypeOf :: ExpI -> Repl ()
doTypeOf e = do
    envs <- lift $ gets stateEnv
    ms   <- liftIO $ typeOfWithEnv envs e
    case ms of
      Left err    -> spew err
      Right sigma -> spew (showType sigma)

doReset :: Repl ()
doReset = lift $ do
    libDirs <- gets stateLibDirs
    modify (setEnv $ setLibDirs libDirs initEnvironments)

doDumpEnv :: Repl ()
doDumpEnv = do
  envs <- lift $ gets stateEnv
  forM_ (dumpTypeEnv envs) $ \(name, sigma) ->
      spew $ name ++ " : " ++ showType sigma

parseLine :: String -> Either String Line
parseLine str
  | all isSpace str = return NoOp
  | otherwise = showError $ P.parse (topLevel pLine) "<interactive>" str

pLine :: Parser Line
pLine = pCommand <|> P.try pTerm <|> pDecl <|> pTypeDecl

pTerm :: Parser Line
pTerm = Term <$> pExp

pDecl :: Parser Line
pDecl = (\(b, mt, e) -> Decl b mt e)
    <$> (reserved "let" *> pLetDecl)

pTypeDecl :: Parser Line
pTypeDecl = TypeDecl <$> pSynonymDecl

pCommand :: Parser Line
pCommand = Command <$> (reservedOp ":" *> p)
  where
    p =  (reserved "peek"  <|> reserved "p") *> (Peek      <$> pExp)
     <|> (reserved "type"  <|> reserved "t") *> (Type      <$> pExp)
     <|> (reserved "load"  <|> reserved "l") *> (Load      <$> pFilePath)
     <|> reserved "cd"                       *> (ChangeCWD <$> pFilePath)
     <|> (reserved "reset" <|> reserved "r") *> pure Reset
     <|> (reserved "env"   <|> reserved "e") *> pure DumpEnv
     <|> (reserved "quit"  <|> reserved "q") *> pure Quit
     <|> (reserved "help"
          <|> reserved "h" <|> reserved "?") *> pure Help
     <|> reserved "{"                        *> pure BeginMulti

pFilePath :: Parser FilePath
pFilePath = stringLiteral -- TODO

setMode :: Mode -> ReplState -> ReplState
setMode m s = s { stateMode = m }

setEnv :: Environments -> ReplState -> ReplState
setEnv envs s = s { stateEnv = envs }

addToBuffer :: String -> ReplState -> ReplState
addToBuffer str s = s { stateBuffer = stateBuffer s ++ [str] }

doEndMulti :: Repl ()
doEndMulti = do
  str <- lift $ gets (unlines . stateBuffer)
  lift $ modify $ clearBuffer . setMode SingleLine
  process str

clearBuffer :: ReplState -> ReplState
clearBuffer s = s { stateBuffer = mempty }

isEndMulti :: String -> Bool
isEndMulti ":}" = True
isEndMulti _    = False

spew :: String -> Repl ()
spew = HL.outputStrLn

whenJust :: Applicative m => Maybe a -> (a -> m ()) -> m ()
whenJust mg f = maybe (pure ()) f mg
