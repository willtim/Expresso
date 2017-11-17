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

module Expresso.Syntax where

import Text.Parsec (SourcePos)
import Text.Parsec.Pos (newPos)

import Expresso.Utils

type Pos    = SourcePos
type Label  = String
type Name   = String

type ExpI = Fix ((ExpF Name Bind :+: K Import) :*: K Pos)
type Exp  = Fix (ExpF Name Bind :*: K Pos)
type Exp' = Fix (ExpF Name Bind)

newtype Import = Import { unImport :: FilePath }

data ExpF v b r
  = EVar  v
  | EPrim Prim
  | EApp  r r
  | ELam  (b v) r
  | ELet  (b v) r r
  deriving (Show, Functor, Foldable, Traversable)

data Bind v
  = Arg v
  | RecArg [v]
  | RecWildcard
  deriving Show

data Prim
  = Int Integer
  | Bool Bool
  | Char Char
  | String String
  | Trace
  | ErrorPrim
  | Neg
  | Add
  | Sub
  | Mul
  | Div
  | Cond
  | FixPrim
  | FwdComp
  | BwdComp
  | ListEmpty
  | ListCons
  | ListNull
  | ListAppend
  | ListFoldr
  | RecordEmpty -- a.k.a. Unit
  | RecordSelect Label
  | RecordExtend Label
  | RecordRestrict Label
  | EmptyAlt
  | VariantInject Label
  | VariantEmbed Label
  | VariantElim Label
  deriving (Eq, Ord, Show)

dummyPos :: SourcePos
dummyPos = newPos "<Unknown>" 1 1

-- | strip source location annotations
stripPos :: forall f. Functor f => Fix (f :*: K Pos) -> Fix f
stripPos = cata alg where
  alg :: (f :*: K Pos) (Fix f) -> Fix f
  alg (e :*: _) = Fix e

annPos :: forall f. Functor f => Pos -> Fix f -> Fix (f :*: K Pos)
annPos pos = cata alg where
  alg :: f (Fix (f :*: K Pos)) -> Fix (f :*: K Pos)
  alg e = Fix (e :*: K pos)

-- | retrieve source location annotation
getPos :: Fix (f :*: K Pos) -> Pos
getPos = unK . right . unFix

-- | add source location annotation
withPos :: Pos -> f (Fix (f :*: K Pos) )-> Fix (f :*: K Pos)
withPos pos e = Fix (e :*: K pos)


----------------------------------------------------------------------
-- Examples

{-
e1 = EApp (EApp (EPrim $ RecordExtend "y") (EPrim $ Int 2)) (EPrim RecordEmpty)
e2 = EApp (EApp (EPrim $ RecordExtend "x") (EPrim $ Int 1)) e1
e3 = EApp (EPrim $ RecordSelect "y") e2
e4 = ELet (Arg "f") (ELam (Arg "r") (EApp (EPrim $ RecordSelect "x") (EVar "r"))) (EVar "f")
e5 = ELam (Arg "r") (EApp (EPrim $ RecordSelect "x") (EVar "r"))
e6 = ELam (Arg "r") $ app (EPrim Add) [ EApp (EPrim $ RecordSelect "x") (EVar "r")
                                , EApp (EPrim $ RecordSelect "y") (EVar "r")]

-- Row tail unification soundness
-- \r -> if True then { x = 1 | r } else { y = 2 | r }
e7 = ELam (Arg "r") $ app (EPrim Cond)
       [ EPrim $ Bool True
       , app (EPrim $ RecordExtend "x") [EPrim $ Int 1, EVar "r"]
       , app (EPrim $ RecordExtend "y") [EPrim $ Int 2, EVar "r"]
       ]

-- Record arguments
e8 = ELam (RecArg ["x", "y"]) $ app (EPrim Add) [(EVar "x"), (EVar "y")]

-- Record argument field-pun generalisation
e9 = ELet (RecArg ["id"]) (app (EPrim $ RecordExtend "id") [ELam (Arg "a") (EVar "a"), EPrim RecordEmpty]) (EVar "id")

app :: Exp -> [Exp] -> Exp
app f = foldl EApp f

-- -- Fail in empty row case
-- \x -> case x of A -> 1, B -> 2, A -> 3
-- -- Fail in row var case
-- \x -> <A, B, A | x>
-- -- Failed row rewrite due to row constraints
-- let f = \x -> case <A|x> of B -> 1, _ -> 2 in
-- let g = \x -> case <B|x> of A -> 1, _ -> 2 in
-- \x -> f x + f x

-}
