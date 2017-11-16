{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Expresso.Type where

import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Set as S

import Data.Foldable (fold)
import Data.Monoid

import Expresso.Pretty
import Expresso.Syntax
import Expresso.Utils

type Type = Fix (TypeF :*: K Pos)
type Type' = Fix TypeF

data TypeF r
  = TVarF TyVar
  | TIntF
  | TBoolF
  | TCharF
  | TFunF r r
  | TListF r
  | TRecordF r
  | TVariantF r
  | TRowEmptyF
  | TRowExtendF Label r r
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data TyVar = TyVar
  { tyvarName       :: Name
  , tyvarUnique     :: Int
  , tyvarKind       :: Kind
  , tyvarConstraint :: Constraint
  } deriving (Eq, Ord, Show)

-- | row type variables may have constraints
data Kind = Star | Row deriving (Eq, Ord, Show)

-- | labels the associated tyvar must lack, for types of kind row
type Constraint = S.Set Label

data Scheme = Scheme [TyVar] Type

newtype TypeEnv = TypeEnv { unTypeEnv :: M.Map Name Scheme }
    deriving (Monoid)

instance View TypeF Type where
  proj    = left . unFix
  inj  e  = Fix (e :*: K dummyPos)

instance View TypeF Type' where
  proj = unFix
  inj  = Fix

pattern TVar v             <- (proj -> (TVarF v)) where
  TVar v = inj (TVarF v)
pattern TInt               <- (proj -> TIntF) where
  TInt = inj TIntF
pattern TBool              <- (proj -> TBoolF) where
  TBool = inj TBoolF
pattern TChar              <- (proj -> TCharF) where
  TChar = inj TCharF
pattern TFun t1 t2         <- (proj -> (TFunF t1 t2)) where
  TFun t1 t2 = inj (TFunF t1 t2)
pattern TList t            <- (proj -> (TListF t)) where
  TList t = inj (TListF t)
pattern TRecord t          <- (proj -> (TRecordF t)) where
  TRecord t = inj (TRecordF t)
pattern TVariant t         <- (proj -> (TVariantF t)) where
  TVariant t = inj (TVariantF t)
pattern TRowEmpty          <- (proj -> TRowEmptyF) where
  TRowEmpty = inj TRowEmptyF
pattern TRowExtend l t1 t2 <- (proj -> (TRowExtendF l t1 t2)) where
  TRowExtend l t1 t2 = inj (TRowExtendF l t1 t2)

class Types a where
  ftv :: a -> S.Set TyVar -- ^ free type variables
  apply :: Subst -> a -> a

instance Types Type where
  ftv = cata alg . stripPos where
    alg :: TypeF (S.Set TyVar) -> (S.Set TyVar)
    alg (TVarF v) = S.singleton v
    alg e         = fold e

  apply s = cata alg where
    alg :: (TypeF :*: K Pos) Type -> Type
    alg (TVarF v :*: p) =
        case IM.lookup (tyvarUnique v) (unSubst s) of
            Nothing -> Fix (TVarF v :*: p)
            Just t  -> apply s t -- NOTE
    alg e = Fix e

instance Types Scheme where
  ftv (Scheme vars t) = (ftv t) S.\\ (S.fromList vars)
  apply (Subst s) (Scheme vars t) =
      Scheme vars (apply (Subst $ foldr IM.delete s (map tyvarUnique vars)) t)

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv (M.elems env)
  apply s (TypeEnv env) = TypeEnv (M.map (apply s) env)

instance Types a => Types [a] where
  apply s = map (apply s)
  ftv l   = foldMap ftv l

newtype Subst = Subst { unSubst :: IM.IntMap Type }

nullSubst :: Subst
nullSubst = Subst IM.empty

infixr 0 |->
(|->) :: TyVar -> Type -> Subst
(|->) v t = Subst $ IM.singleton (tyvarUnique v) t

isInSubst :: TyVar -> Subst -> Bool
isInSubst v = IM.member (tyvarUnique v) . unSubst

-- | apply s1 and then s2
-- NB: order is important
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Subst $ (IM.map (apply s1) $ unSubst s2) `IM.union` unSubst s1

instance Monoid Subst where
    mempty  = nullSubst
    mappend = composeSubst

--  | decompose a row-type into its constituent parts
toList :: Type -> ([(Label, Type)], Maybe TyVar)
toList (TVar v)           = ([], Just v)
toList TRowEmpty          = ([], Nothing)
toList (TRowExtend l t r) =
    let (ls, mv) = toList r
    in ((l, t):ls, mv)
toList t = error $ "Unexpected row type: " ++ show (ppType t)

lacks :: Label -> Constraint
lacks = S.singleton

mkRowType :: Type -> [(Label, Type)] -> Type
mkRowType = foldr $ \(l, t@(getPos -> pos)) r ->
    Fix (TRowExtendF l t r :*: K pos)

rowToMap :: Type -> M.Map Name Type
rowToMap (TRowExtend l t r) = M.insert l t (rowToMap r)
rowToMap TRowEmpty          = M.empty
rowToMap TVar{}             = M.empty -- default any row vars to empty row
rowToMap t                  = error $ "Unexpected row type: " ++ show (ppType t)


------------------------------------------------------------
-- Pretty-printing

ppType :: Type -> Doc
ppType (TVar v)     = text $ tyvarName v <> show (tyvarUnique v)
ppType TInt         = "Int"
ppType TBool        = "Bool"
ppType TChar        = "Char"
ppType (TFun t s)   = ppParenType t <+> "->" <+> ppType s
ppType (TList a)    = brackets $ ppType a
ppType (TRecord r)  = braces $ ppRowType r
ppType (TVariant r) = angles $ ppRowType r
ppType TRowEmpty    = "(||)"
ppType (TRowExtend l a r) = "(|" <> text l <> ":" <> ppType a <> "|" <> ppType r <> "|)"
ppType t = error $ "Unexpected type: " ++ show t

ppRowType :: Type -> Doc
ppRowType r = sepBy comma (map ppEntry ls)
           <> maybe mempty (ppRowTail ls) mv
  where
    (ls, mv)       = toList r
    ppRowVar r     = ppType (TVar r)
    ppRowTail [] r = ppRowVar r
    ppRowTail _  r = mempty <+> "|" <+> ppRowVar r
    ppEntry (l, t) = text l <+> ":" <+> ppType t

ppParenType :: Type -> Doc
ppParenType t =
  case t of
    TFun {} -> parens $ ppType t
    _       -> ppType t

-- instance Show Scheme where
--   showsPrec _ x = shows $ ppScheme x

ppScheme :: Scheme -> Doc
ppScheme (rename -> Scheme vars t)
  | null vars = ppType t
  | otherwise = "forall" <+> (catBy space $ map (ppType . TVar) vars) <> dot
                         <>  (let cs = concatMap ppConstraint vars
                              in if null cs then mempty else space <> (parensList cs <+> "=>"))
                         <+> ppType t
  where
    ppConstraint :: TyVar -> [Doc]
    ppConstraint v@(TyVar _ _ k c) =
      case k of
        Star            -> []
        Row | null ls   -> []
            | otherwise -> [catBy "\\" $ ppType (TVar v) : map text ls]
      where
        ls = S.toList c

-- | alpha rename of type vars
rename :: Scheme -> Scheme
rename (Scheme vars t) = Scheme vars' t'
  where
    vars' = zipWith renameTyVar vars [1..]

    renameTyVar (TyVar n _ k c) i = TyVar n i k c

    m = IM.fromList $ zip (map tyvarUnique vars) vars'
    t' = cata alg t where
      alg :: (TypeF :*: K Pos) Type -> Type
      alg (TVarF v :*: pos) | Just v' <- IM.lookup (tyvarUnique v) m
            = Fix (TVarF v' :*: pos)
      alg t = Fix t
