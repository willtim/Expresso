{-# LANGUAGE TupleSections #-}
{-# LANGUAGE PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

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
  , Env
  , Environments
  , Exp
  , ExpF(..)
  , ExpI
  , HasValue(..)
  , Import(..)
  , Name
  , Thunk(..)
  , TIState
  , Type
  , pattern TForAll
  , pattern TVar
  , pattern TMetaVar
  , pattern TInt
  , pattern TDbl
  , pattern TBool
  , pattern TChar
  , pattern TText
  , pattern TFun
  , pattern TList
  , pattern TRecord
  , pattern TVariant
  , pattern TRowEmpty
  , pattern TRowExtend
  , TypeF(..)
  , TypeEnv
  , Value(..)
  , bind
  , dummyPos
  , evalFile
  , evalFile'
  , evalString
  , evalString'
  , evalWithEnv
  , initEnvironments
  , installBinding
  , runEvalM
  , showType
  , showValue
  , showValue'
  , dumpTypeEnv
  , typeOf
  , typeOfString
  , typeOfWithEnv
  , validate
  , Eval.choice
  , Eval.mkRecord
  , Eval.mkStrictLam
  , Eval.mkStrictLam2
  , Eval.mkStrictLam3
  , Eval.mkVariant
  , Eval.typeMismatch
  , Eval.unit
  , (Eval..:)
  , (Eval..=)
  ) where

import Control.Monad ((>=>))
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)

import Expresso.Eval (Env, EvalM, HasValue(..), Thunk(..), Value(..), insertEnv, runEvalM)
import Expresso.TypeCheck (TIState, initTIState)
import Expresso.Pretty (render)
import Expresso.Syntax
import Expresso.Type
import Expresso.Utils
import qualified Expresso.Eval as Eval
import qualified Expresso.TypeCheck as TypeCheck
import qualified Expresso.Parser as Parser

-- | Type and term environments.
data Environments = Environments
    { envsTypeEnv :: !TypeEnv
    , envsTIState :: !TIState
    , envsTermEnv :: !Env
    }

-- | Empty initial type and term environments.
initEnvironments :: Environments
initEnvironments = Environments mempty initTIState mempty

-- | Install a binding using the supplied name, type and term.
-- Useful for extending the set of built-in functions.
installBinding :: Name -> Type -> Value -> Environments -> Environments
installBinding name ty val envs =
    envs { envsTypeEnv = insertTypeEnv name ty (envsTypeEnv envs)
         , envsTermEnv = insertEnv name (Thunk . return $ val) (envsTermEnv envs)
         }

-- | Query the type of an expression using the supplied type environment.
typeOfWithEnv :: Environments -> ExpI -> IO (Either String Type)
typeOfWithEnv (Environments tEnv tState _) ei = runExceptT $ do
    e <- Parser.resolveImports ei
    ExceptT $ return $ inferTypes tEnv tState e

-- | Query the type of an expression.
typeOf :: ExpI -> IO (Either String Type)
typeOf = typeOfWithEnv initEnvironments

-- | Parse an expression and query its type.
typeOfString :: String -> IO (Either String Type)
typeOfString str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ typeOf top

-- | Evaluate an expression using the supplied type and term environments.
evalWithEnv
    :: HasValue a
    => Environments
    -> ExpI
    -> IO (Either String a)
evalWithEnv (Environments tEnv tState env) ei = runExceptT $ do
  e      <- Parser.resolveImports ei
  _sigma <- ExceptT . return $ inferTypes tEnv tState e
  ExceptT $ runEvalM . (Eval.eval env >=> Eval.proj) $ e

-- | Evaluate the contents of the supplied file path; and optionally
-- validate using a supplied type (schema).
evalFile :: HasValue a => Maybe Type -> FilePath -> IO (Either String a)
evalFile = evalFile' initEnvironments

-- | Evaluate the contents of the supplied file path; and optionally
-- validate using a supplied type (schema).
-- NOTE: This version also takes a term environment and a type environment
-- so that foreign functions and their types can be installed respectively.
evalFile' :: HasValue a => Environments -> Maybe Type -> FilePath -> IO (Either String a)
evalFile' envs mty path = runExceptT $ do
    top <- ExceptT $ Parser.parse path <$> readFile path
    ExceptT $ evalWithEnv envs (maybe id validate mty $ top)

-- | Parse an expression and evaluate it; optionally
-- validate using a supplied type (schema).
evalString :: HasValue a => Maybe Type -> String -> IO (Either String a)
evalString = evalString' initEnvironments

-- | Parse an expression and evaluate it; optionally
-- validate using a supplied type (schema).
-- NOTE: This version also takes a term environment and a type environment
-- so that foreign functions and their types can be installed respectively.
evalString' :: HasValue a => Environments -> Maybe Type -> String -> IO (Either String a)
evalString' envs mty str = runExceptT $ do
    top <- ExceptT $ return $ Parser.parse "<unknown>" str
    ExceptT $ evalWithEnv envs (maybe id validate mty $ top)

-- | Add a validating type signature section to the supplied expression.
validate :: Type -> ExpI -> ExpI
validate ty e = Parser.mkApp pos (Parser.mkSigSection pos ty) [e]
  where
    pos = dummyPos

-- | Used by the REPL to bind variables.
bind
    :: Environments
    -> Bind Name
    -> Maybe Type
    -> ExpI
    -> EvalM Environments
bind (Environments tEnv tState env) b mty ei = do
    e     <- Parser.resolveImports ei
    let (res'e, tState') =
            TypeCheck.runTI (TypeCheck.tcDecl (getAnn ei) b mty e) tEnv tState
    case res'e of
        Left err    -> throwError err
        Right tEnv' -> do
            thunk <- Eval.mkThunk $ Eval.eval env e
            env'  <- Eval.bind env b thunk
            return $ Environments tEnv' tState' env'

-- | Pretty print the supplied type.
showType :: Type -> String
showType = render . ppType

-- | Pretty print the supplied value. This does *not* evaluate deeply.
showValue :: Value -> String
showValue = render . Eval.ppValue

-- | Pretty print the supplied value. This evaluates deeply.
showValue' :: Value -> IO String
showValue' v = either id render <$> (runEvalM $ Eval.ppValue' v)

-- | Extract type environment bindings.
dumpTypeEnv :: Environments -> [(Name, Sigma)]
dumpTypeEnv = typeEnvToList . envsTypeEnv

inferTypes :: TypeEnv -> TIState -> Exp -> Either String Type
inferTypes tEnv tState e =
    fst $ TypeCheck.runTI (TypeCheck.typeCheck e) tEnv tState
