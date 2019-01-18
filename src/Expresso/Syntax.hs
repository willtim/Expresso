{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Expresso.Syntax
-- Copyright   : (c) Tim Williams 2017-2019
-- License     : BSD3
--
-- Maintainer  : info@timphilipwilliams.com
-- Stability   : experimental
-- Portability : portable
--
-- The abstract syntax for expressions in Expresso.
--
module Expresso.Syntax where

import Data.Text (Text)
import Expresso.Type
import Expresso.Utils

-- | Expressions with imports.
type ExpI  = Fix ((ExpF Name Bind Type :+: K Import) :*: K Pos)

-- | Expressions with imports resolved.
type Exp   = Fix (ExpF Name Bind Type :*: K Pos)

-- | An import file path.
newtype Import = Import { unImport :: FilePath }

-- | Pattern functor representing expressions and parameterised with
-- the type of variable @v@, type of binder @b@ and the type of
-- type-annotation @t@.
data ExpF v b t r
  = EVar  v
  | EPrim Prim
  | EApp  r r
  | ELam  (b v) r
  | EAnnLam (b v) t r
  | ELet  (b v) r r
  | EAnnLet (b v) t r r
  | EAnn  r t
  deriving (Show, Functor, Foldable, Traversable)

-- | Binders
data Bind v
  = Arg v
  | RecArg [v]
  | RecWildcard
  deriving Show

-- | Language primitives
data Prim
  = Int Integer
  | Dbl Double
  | Bool Bool
  | Char Char
  | Text Text
  | Show
  | Trace
  | ErrorPrim
  | ArithPrim ArithOp
  | RelPrim   RelOp
  | Not
  | And
  | Or
  | Eq
  | NEq
  | Double      -- double from int
  | Floor
  | Ceiling
  | Abs
  | Neg
  | Mod
  | Cond
  | FixPrim
  | FwdComp
  | BwdComp
  | Pack
  | Unpack
  | TextAppend
  | ListEmpty
  | ListCons
  | ListNull    -- needed if list elems have no equality defined
  | ListAppend
  | ListFoldr
  | RecordEmpty -- a.k.a. Unit
  | RecordSelect Label
  | RecordExtend Label
  | RecordRestrict Label
  | Absurd
  | VariantInject Label
  | VariantEmbed Label
  | VariantElim Label
  deriving (Eq, Ord, Show)

data ArithOp = Add | Mul | Sub | Div
  deriving (Eq, Ord, Show)

data RelOp   = RGT  | RGTE | RLT  | RLTE
  deriving (Eq, Ord, Show)
