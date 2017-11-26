{-# LANGUAGE ScopedTypeVariables #-}

------------------------------------------------------------
-- Expresso Read-Eval-Print-Loop
--
module Main where

import Control.Applicative
import Control.Monad (forM_)
import Control.Monad.IO.Class
import Control.Monad.State.Strict
import Data.Char
import System.Console.Haskeline (InputT)
import System.Console.Haskeline.MonadException ()
import System.Directory
import System.FilePath
import Text.Parsec.String (Parser)
import qualified Data.Map as M
import qualified System.Console.Haskeline as HL
import qualified Text.Parsec as P

import Expresso
import Expresso.Parser ( pExp, pLetDecl, whiteSpace
                       , reserved, reservedOp, stringLiteral
                       )
import Expresso.Utils

ps1 :: String
ps1 = "λ"

data Mode = SingleLine | MultiLine | Quitting

data ReplState = ReplState
  { stateMode    :: Mode
  , stateBuffer  :: [String]
  , stateEnv     :: (TypeEnv, TIState, Env)
  }

data Command
  = Peek      ExpI
  | Type      ExpI
  | ChangeCWD FilePath
  | BeginMulti
  | Reset
  | Env
  | Quit
  | Help

data Line
  = Command Command
  | Term ExpI
  | Decl (Bind Name) ExpI
  | NoOp

type Repl = InputT (StateT ReplState IO)

main :: IO ()
main = do
  cwd <- liftIO getCurrentDirectory
  let preludePath = cwd </> "Prelude.x"
  runRepl $ do
    mapM_ spew
      [ "Expresso REPL"
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
    Left err            -> spew err
    Right (Command c)   -> doCommand c
    Right (Term e)      -> doEval showValue' e
    Right (Decl b e)    -> doDecl b e
    Right NoOp          -> return ()
 `HL.catch` handler
  where
    handler :: HL.SomeException -> Repl ()
    handler ex = spew $ "Caught exception: " ++ show ex

runRepl :: Repl a -> IO a
runRepl m = do
    historyFile <- (</> ".expresso_history") <$> getHomeDirectory
    let settings = HL.defaultSettings {HL.historyFile = Just historyFile}
    evalStateT (HL.runInputT settings m) emptyReplState

emptyReplState :: ReplState
emptyReplState = ReplState
  { stateMode   = SingleLine
  , stateBuffer = mempty
  , stateEnv    = (mempty, initTIState, mempty)
  }

loadPrelude :: FilePath -> Repl ()
loadPrelude path = do
  doDecl RecWildcard $ Fix (InR (K (Import path)) :*: K dummyPos)
  spew $ "Loaded Prelude from " ++ path

doCommand :: Command -> Repl ()
doCommand c = case c of
  Peek e         -> doEval (return . showValue) e
  Type e         -> doTypeOf e
  ChangeCWD path -> liftIO $ setCurrentDirectory path
  Quit           -> lift $ modify (setMode Quitting)
  BeginMulti     -> lift $ modify (setMode MultiLine)
  Reset          -> doReset
  Env            -> doDumpEnv
  Help           -> mapM_ spew
    [ "REPL commands available from the prompt:"
    , ""
    , "<expression>                evaluate an expression"
    , ":peek <expression>          evaluate, but not deeply"
    , ":{\\n ..lines.. \\n:}\\n       multiline command"
    , ":cd <path>                  change current working directory"
    , ":type <term>                show the type of <term>"
    , ":reset                      reset REPL, unloading all definitions"
    , ":env                        dump bound symbols in the environment"
    , ":quit                       exit REPL"
    , ":help                       display this list of commands"
    , ""
    ]

instance FromExpresso Value -- FIXME

doEval :: (Value -> IO String) -> ExpI -> Repl ()
doEval pp e = do
  envs <- lift $ gets stateEnv
  v'e  <- liftIO $ evalWithEnv envs e
  case v'e of
      Left err  -> spew err
      Right val -> liftIO (pp val) >>= spew

doDecl :: Bind Name -> ExpI -> Repl ()
doDecl b e = do
  envs   <- lift $ gets stateEnv
  envs'e <- liftIO $ fmap pure $ bind envs b e
  case envs'e of
      Left err    -> spew err
      Right envs' -> lift $ modify (setEnv envs')

doTypeOf :: ExpI -> Repl ()
doTypeOf e = do
    (tEnv, tState, _) <- lift $ gets stateEnv
    ms <- liftIO $ typeOfWithEnv tEnv tState e
    case ms of
      Left err  -> spew err
      Right sch -> spew (showType sch)

doReset :: Repl ()
doReset = lift $ modify (setEnv $ stateEnv emptyReplState)

doDumpEnv :: Repl ()
doDumpEnv = do
  (TypeEnv binds, _, _) <- lift $ gets stateEnv
  forM_ (M.toList binds) $ \(name, sch) ->
      spew $ name ++ " : " ++ showType sch

parseLine :: String -> Either String Line
parseLine str
  | all isSpace str = return NoOp
  | otherwise = showError $ P.parse (whiteSpace *> pLine <* P.eof) "<interactive>" str

pLine :: Parser Line
pLine = pCommand <|> P.try pTerm <|> pDecl

pTerm :: Parser Line
pTerm = Term <$> pExp

pDecl :: Parser Line
pDecl = uncurry Decl <$> (reserved "let" *> pLetDecl)

pCommand :: Parser Line
pCommand = Command <$> (reservedOp ":" *> p)
  where
    p =  (reserved "peek"  <|> reserved "p") *> (Peek      <$> pExp)
     <|> (reserved "type"  <|> reserved "t") *> (Type      <$> pExp)
     <|> reserved "cd"                       *> (ChangeCWD <$> pFilePath)
     <|> (reserved "reset" <|> reserved "r") *> pure Reset
     <|> (reserved "env"   <|> reserved "e") *> pure Env
     <|> (reserved "quit"  <|> reserved "q") *> pure Quit
     <|> (reserved "help"
          <|> reserved "h" <|> reserved "?") *> pure Help
     <|> reserved "{"                        *> pure BeginMulti

pFilePath :: Parser FilePath
pFilePath = stringLiteral -- TODO

setMode :: Mode -> ReplState -> ReplState
setMode m s = s { stateMode = m }

setEnv :: (TypeEnv, TIState, Env) -> ReplState -> ReplState
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
