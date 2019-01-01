{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Expresso
-- Copyright   : (c) Tim Williams 2017-2019
-- License     : BSD3
--
-- Maintainer  : info@timphilipwilliams.com
-- Stability   : experimental
-- Portability : portable
--
-- A simple expressions language with polymorphic extensible row types.
--
-- This module is the public API for Expresso.
--
module Expresso
  ( ExpF(..)
  , Bind(..)
  , Import(..)
  , ExpI
  , Exp
  , Env
  , HasValue(..)
  , Value(..)
  , Name
  , TypeEnv(..)
  , TIState
  , bind
  , dummyPos
  , eval
  , evalFile
  , evalFile'
  , evalString
  , evalWithEnv
  , initTIState
  , runEvalM
  , showType
  , showValue
  , showValue'
  , typeOf
  , typeOfString
  , typeOfWithEnv
  , validate
  ) where

import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)

import Expresso.Eval (Env, EvalM, HasValue(..), Value(..), runEvalM)
import Expresso.TypeCheck (TIState, initTIState)
import Expresso.Pretty (render)
import Expresso.Syntax
import Expresso.Type
import Expresso.Utils
import qualified Expresso.Eval as Eval
import qualified Expresso.TypeCheck as TypeCheck
import qualified Expresso.Parser as Parser


-- | Query the type of an expression using the supplied type environment.
typeOfWithEnv :: TypeEnv -> TIState -> ExpI -> IO (Either String Type)
typeOfWithEnv tEnv tState ei = runExceptT $ do
    e <- Parser.resolveImports ei
    ExceptT $ return $ inferTypes tEnv tState e

-- | Query the type of an expression.
typeOf :: ExpI -> IO (Either String Type)
typeOf = typeOfWithEnv mempty initTIState

-- | Parse an expression and query its type.
typeOfString :: String -> IO (Either String Type)
typeOfString str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ typeOf top

-- | Evaluate an expression using the supplied type and term environments.
evalWithEnv
    :: HasValue a
    => (TypeEnv, TIState, Env)
    -> ExpI
    -> IO (Either String a)
evalWithEnv (tEnv, tState, env) ei = runExceptT $ do
  e      <- Parser.resolveImports ei
  _sigma <- ExceptT . return $ inferTypes tEnv tState e
  ExceptT $ runEvalM . (Eval.eval env >=> Eval.proj) $ e

-- | Evaluate an expression.
eval :: HasValue a => ExpI -> IO (Either String a)
eval = evalWithEnv (mempty, initTIState, mempty)

-- | Evaluate the contents of the supplied file path.
evalFile :: HasValue a => FilePath -> IO (Either String a)
evalFile path = runExceptT $ do
    top <- ExceptT $ Parser.parse path <$> readFile path
    ExceptT $ eval top

-- | Evaluate the contents of the supplied file path; and validate
-- using the supplied type (schema).
evalFile' :: HasValue a => Type -> FilePath -> IO (Either String a)
evalFile' ty path = runExceptT $ do
    top <- ExceptT $ Parser.parse path <$> readFile path
    ExceptT $ eval (validate ty top)

-- | Add a validating type signature section to the supplied expression.
validate :: Type -> ExpI -> ExpI
validate ty e = Parser.mkApp pos (Parser.mkSigSection pos ty) [e]
  where
    pos = dummyPos

-- | Parse an expression and evaluate it.
evalString :: HasValue a => String -> IO (Either String a)
evalString str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ eval top

-- | Used by the REPL to bind variables.
bind
    :: (TypeEnv, TIState, Env)
    -> Bind Name
    -> ExpI
    -> EvalM (TypeEnv, TIState, Env)
bind (tEnv, tState, env) b ei = do
    e     <- Parser.resolveImports ei
    let (res'e, tState') =
            TypeCheck.runTI (TypeCheck.tcDecl (getAnn ei) b e) tEnv tState
    case res'e of
        Left err    -> throwError err
        Right tEnv' -> do
            thunk <- Eval.mkThunk $ Eval.eval env e
            env'  <- Eval.bind env b thunk
            return (tEnv', tState', env')

-- | Pretty print the supplied type.
showType :: Type -> String
showType = render . ppType

-- | Pretty print the supplied value. This does *not* evaluate deeply.
showValue :: Value -> String
showValue = render . Eval.ppValue

-- | Pretty print the supplied value. This evaluates deeply.
showValue' :: Value -> IO String
showValue' v = either id render <$> (runEvalM $ Eval.ppValue' v)

inferTypes :: TypeEnv -> TIState -> Exp -> Either String Type
inferTypes tEnv tState e =
    fst $ TypeCheck.runTI (TypeCheck.typeCheck e) tEnv tState
