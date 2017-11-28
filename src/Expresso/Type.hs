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

import Text.Parsec (SourcePos)
import Text.Parsec.Pos (newPos)

import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Set as S

import Data.Foldable (fold)
import Data.Monoid

import Expresso.Pretty
import Expresso.Utils

type Pos    = SourcePos
type Label  = String
type Name   = String

type Type = Fix (TypeF :*: K Pos)
type Type' = Fix TypeF

data TypeF r
  = TVarF TyVar
  | TIntF
  | TDblF
  | TBoolF
  | TCharF
  | TFunF r r
  | TMaybeF r
  | TListF r
  | TRecordF r
  | TVariantF r
  | TRowEmptyF
  | TRowExtendF Label r r
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

data TyVar = TyVar
  { tyvarName       :: Name
  , tyvarUnique     :: Int
  , tyvarConstraint :: Constraint
  } deriving (Eq, Ord, Show)

-- | Type variable constraints
-- e.g. for types of kind row, labels the associated tyvar must lack
data Constraint
    = Row  (S.Set Label)
    | Star StarHierarchy
    deriving (Eq, Ord, Show)

-- | A simple hierarchy. i.e. Num has Ord and Eq, Ord has Eq.
data StarHierarchy
    = None
    | CEq
    | COrd
    | CNum
    deriving (Eq, Ord, Show)

data Scheme = Scheme [TyVar] Type

getMonomorphic :: Scheme -> Maybe Type
getMonomorphic (Scheme [] t) = Just t
getMonomorphic _ = Nothing

newtype TypeEnv = TypeEnv { unTypeEnv :: M.Map Name Scheme }
    deriving (Monoid)

instance View TypeF Type where
  proj    = left . unFix
  toValue  e  = Fix (e :*: K dummyPos)

dummyPos :: Pos
dummyPos = newPos "<unknown>" 1 1

instance View TypeF Type' where
  proj = unFix
  toValue  = Fix

pattern TVar v             <- (proj -> (TVarF v)) where
  TVar v = toValue (TVarF v)
pattern TInt               <- (proj -> TIntF) where
  TInt = toValue TIntF
pattern TDbl               <- (proj -> TDblF) where
  TDbl = toValue TDblF
pattern TBool              <- (proj -> TBoolF) where
  TBool = toValue TBoolF
pattern TChar              <- (proj -> TCharF) where
  TChar = toValue TCharF
pattern TFun t1 t2         <- (proj -> (TFunF t1 t2)) where
  TFun t1 t2 = toValue (TFunF t1 t2)
pattern TMaybe t           <- (proj -> (TMaybeF t)) where
  TMaybe t = toValue (TMaybeF t)
pattern TList t            <- (proj -> (TListF t)) where
  TList t = toValue (TListF t)
pattern TRecord t          <- (proj -> (TRecordF t)) where
  TRecord t = toValue (TRecordF t)
pattern TVariant t         <- (proj -> (TVariantF t)) where
  TVariant t = toValue (TVariantF t)
pattern TRowEmpty          <- (proj -> TRowEmptyF) where
  TRowEmpty = toValue TRowEmptyF
pattern TRowExtend l t1 t2 <- (proj -> (TRowExtendF l t1 t2)) where
  TRowExtend l t1 t2 = toValue (TRowExtendF l t1 t2)

class Types a where
  ftv :: a -> S.Set TyVar -- ^ free type variables
  apply :: Subst -> a -> a

instance Types Type where
  ftv = cata alg . stripAnn where
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

lacks :: [Label] -> Constraint
lacks = Row . S.fromList

mkRowType :: Type -> [(Label, Type)] -> Type
mkRowType = foldr $ \(l, t@(getAnn -> pos)) r ->
    Fix (TRowExtendF l t r :*: K pos)

rowToMap :: Type -> M.Map Name Type
rowToMap (TRowExtend l t r) = M.insert l t (rowToMap r)
rowToMap TRowEmpty          = M.empty
rowToMap TVar{}             = M.empty -- default any row vars to empty row
rowToMap t                  = error $ "Unexpected row type: " ++ show (ppType t)


------------------------------------------------------------
-- Constraints

-- | True if the supplied type of kind Star satisfies the (Star) constraint
satisfies :: Type -> Constraint -> Bool
satisfies t c =
    case (infer t, c) of
        (Star c1, Star c2) -> c1 >= c2
        (c1, c2)  -> error $ "satisfies: kind mismatch: " ++ show (c1, c2)
  where
    infer :: Type -> Constraint
    infer (TVar v)  = tyvarConstraint v
    infer TInt      = Star CNum
    infer TDbl      = Star CNum
    infer TBool     = Star COrd
    infer TChar     = Star COrd
    infer TFun{}    = Star None
    infer (TMaybe t) =
        let Star c = infer t
        in Star (min c COrd)
    infer (TList t) =
        let Star c = infer t
        in Star (min c COrd)
    infer (TRecord r)
        | Just (Star c) <- inferFromRow r = Star (min c CEq)
        | otherwise = Star None
    infer (TVariant r)
        | Just (Star c) <- inferFromRow r = Star (min c CEq)
        | otherwise = Star None
    infer t = error $ "satisfies/infer: unexpected type: " ++ show t

    inferFromRow :: Type -> Maybe Constraint
    inferFromRow TVar{}    = Nothing
    inferFromRow TRowEmpty = Nothing
    inferFromRow (TRowExtend _ t r)
        | Just c <- inferFromRow r = Just $ infer t `unionConstraints` c
        | otherwise = Just $ infer t
    inferFromRow t = error $ "satisfies/inferFromRow: unexpected type: " ++ show t

unionConstraints :: Constraint -> Constraint -> Constraint
unionConstraints (Row s1)  (Row s2) = Row $ s1 `S.union` s2
unionConstraints (Star c1) (Star c2)
    | c1 > c2   = Star c1 -- pick the most specific
    | otherwise = Star c2
unionConstraints c1 c2  = error $ "unionConstraints: kind mismatch: " ++ show (c1, c2)


------------------------------------------------------------
-- Pretty-printing

ppType :: Type -> Doc
ppType (TVar v)     = text $ tyvarName v <> show (tyvarUnique v)
ppType TInt         = "Int"
ppType TDbl         = "Double"
ppType TBool        = "Bool"
ppType TChar        = "Char"
ppType (TFun t s)   = ppParenType t <+> "->" <+> ppType s
ppType (TMaybe t)   = "Maybe" <+> ppType t
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
    ppConstraint v =
      case tyvarConstraint v of
        Row (S.toList -> ls)
            | null ls   -> []
            | otherwise -> [catBy "\\" $ ppType (TVar v) : map text ls]
        Star None -> []
        Star CEq  -> ["Eq"  <+> ppType (TVar v)]
        Star COrd -> ["Ord" <+> ppType (TVar v)]
        Star CNum -> ["Num" <+> ppType (TVar v)]

-- | alpha rename of type vars
rename :: Scheme -> Scheme
rename (Scheme vars t) = Scheme vars' t'
  where
    vars' = zipWith renameTyVar vars [1..]

    renameTyVar (TyVar n _ c) i = TyVar n i c

    m = IM.fromList $ zip (map tyvarUnique vars) vars'
    t' = cata alg t where
      alg :: (TypeF :*: K Pos) Type -> Type
      alg (TVarF v :*: pos) | Just v' <- IM.lookup (tyvarUnique v) m
            = Fix (TVarF v' :*: pos)
      alg t = Fix t

ppStarConstraint :: StarHierarchy -> Doc
ppStarConstraint None = mempty
ppStarConstraint CEq  = "Eq"
ppStarConstraint COrd = "Ord"
ppStarConstraint CNum = "Num"
