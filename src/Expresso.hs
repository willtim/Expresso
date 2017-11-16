{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

------------------------------------------------------------
-- Expresso API (currently used by the REPL)
--
module Expresso
  ( module Expresso.Syntax
  , module Expresso.Eval
  , module Expresso.Type
  , module Expresso.InferType
  , bind
  , eval
  , evalFile
  , evalWithEnv
  , showType
  , showValue
  , showValue'
  , typeOf
  , typeOfWithEnv
  ) where

import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)

import Expresso.Eval (Env, EvalM, HasValue(..), Value(..), runEvalM)
import Expresso.InferType (TIState, initTIState)
import Expresso.Pretty (render)
import Expresso.Syntax
import Expresso.Type
import qualified Expresso.Eval as Eval
import qualified Expresso.InferType as InferType
import qualified Expresso.Parser as Parser


evalFile :: HasValue a => FilePath -> IO (Either String a)
evalFile path = runExceptT $ do
    top <- ExceptT $ Parser.parse path <$> readFile path
    ExceptT $ eval top

typeOf :: ExpI -> IO (Either String Scheme)
typeOf = typeOfWithEnv mempty initTIState

typeOfWithEnv :: TypeEnv -> TIState -> ExpI -> IO (Either String Scheme)
typeOfWithEnv tEnv tState ei = runExceptT $ do
    e <- Parser.resolveImports ei
    ExceptT $ return $ inferType tEnv tState e

evalWithEnv :: HasValue a => (TypeEnv, TIState, Env) -> ExpI -> IO (Either String a)
evalWithEnv (tEnv, tState, env) ei = runExceptT $ do
  e <- Parser.resolveImports ei
  case inferType tEnv tState e of
    Left err -> throwError err
    Right _  -> ExceptT $ runEvalM . (Eval.eval env >=> Eval.proj) $ e

eval :: HasValue a => ExpI -> IO (Either String a)
eval = evalWithEnv (mempty, initTIState, mempty)

-- used by the REPL to bind variables
bind :: (TypeEnv, TIState, Env) -> Bind Name -> ExpI -> EvalM (TypeEnv, TIState, Env)
bind (tEnv, tState, env) b ei = do
    e     <- Parser.resolveImports ei
    let (tEnv'e, tState') = InferType.runTI (InferType.tiDecl (getPos ei) b e) tEnv tState
    case tEnv'e of
        Left err    -> throwError err
        Right tEnv' -> do
            thunk <- Eval.mkThunk $ Eval.eval env e
            env'  <- Eval.bind env b thunk
            return (tEnv', tState', env')

inferType :: TypeEnv -> TIState -> Exp -> Either String Scheme
inferType tEnv tState e = fst $ InferType.runTI (InferType.typeInference e) tEnv tState

showType :: Scheme -> String
showType = render . ppScheme

-- | This does *not* evaluate deeply
showValue :: Value -> String
showValue = render . Eval.ppValue

-- | This evaluates deeply
showValue' :: Value -> IO String
showValue' v = either id render <$> (runEvalM $ Eval.ppValue' v)
