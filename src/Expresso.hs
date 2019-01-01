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
  ( Bind(..)
  , Env(..)
  , Exp
  , ExpF(..)
  , ExpI
  , HasValue(..)
  , Import(..)
  , Name
  , Thunk(..)
  , TIState
  , TypeEnv(..)
  , Value(..)
  , bind
  , dummyPos
  , evalFile
  , evalFile'
  , evalString
  , evalString'
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
  , Eval.mkStrictLam
  , Eval.mkStrictLam2
  , Eval.mkStrictLam3
  ) where

import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)

import Expresso.Eval (Env, EvalM, HasValue(..), Thunk(..), Value(..), runEvalM)
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

-- | Evaluate the contents of the supplied file path; and optionally
-- validate using a supplied type (schema).
evalFile :: HasValue a => Maybe Type -> FilePath -> IO (Either String a)
evalFile = evalFile' mempty mempty

-- | Evaluate the contents of the supplied file path; and optionally
-- validate using a supplied type (schema).
-- NOTE: This version also takes a term environment and a type environment
-- so that foreign functions and their types can be installed respectively.
evalFile' :: HasValue a =>  Env -> TypeEnv -> Maybe Type -> FilePath -> IO (Either String a)
evalFile' env tEnv mty path = runExceptT $ do
    top <- ExceptT $ Parser.parse path <$> readFile path
    ExceptT $ evalWithEnv (tEnv, initTIState, env) (maybe id validate mty $ top)

-- | Parse an expression and evaluate it; optionally
-- validate using a supplied type (schema).
evalString :: HasValue a => Maybe Type -> String -> IO (Either String a)
evalString = evalString' mempty mempty

-- | Parse an expression and evaluate it; optionally
-- validate using a supplied type (schema).
-- NOTE: This version also takes a term environment and a type environment
-- so that foreign functions and their types can be installed respectively.
evalString' :: HasValue a => Env -> TypeEnv -> Maybe Type -> String -> IO (Either String a)
evalString' env tEnv mty str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ evalWithEnv (tEnv, initTIState, env) (maybe id validate mty $ top)

-- | Add a validating type signature section to the supplied expression.
validate :: Type -> ExpI -> ExpI
validate ty e = Parser.mkApp pos (Parser.mkSigSection pos ty) [e]
  where
    pos = dummyPos

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
