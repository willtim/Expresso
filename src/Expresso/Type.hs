{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- |
-- Module      : Expresso.Type
-- Copyright   : (c) Tim Williams 2017-2019
-- License     : BSD3
--
-- Maintainer  : info@timphilipwilliams.com
-- Stability   : experimental
-- Portability : portable
--
-- The abstract syntax for types in Expresso.
--
module Expresso.Type where

import Control.Monad
import Control.Monad.Except
import Data.Data
import Data.Foldable (fold)
import Data.IntMap (IntMap)
import Data.Map (Map)
import Data.Set (Set)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.Set as S

import Text.Parsec (SourcePos)
import Text.Parsec.Pos (newPos)

import Expresso.Pretty
import Expresso.Utils

-- | Source position
type Pos   = SourcePos

-- | Row label
type Label = String

-- | A string representing a unique name.
type Name  = String

-- | Type syntax annotated with source position.
type Type  = Fix (TypeF :*: K Pos)

-- | Unannotated type syntax.
type Type' = Fix TypeF

type Sigma = Type
type Rho   = Type  -- No top-level ForAll
type Tau   = Type  -- No ForAlls anywhere

-- | Pattern functor for the syntax of types.
data TypeF r
  = TForAllF  [TyVar] r
  | TVarF     TyVar
  | TMetaVarF MetaTv
  | TSynonymF Name [r]
  | TIntF
  | TDblF
  | TBoolF
  | TCharF
  | TTextF
  | TFunF r r
  | TListF r
  | TRecordF r
  | TVariantF r
  | TRowEmptyF
  | TRowExtendF Label r r
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable, Data)

type Uniq = Int

data Flavour
  = Bound    -- a type variable bound by a ForAll
  | Skolem   -- a skolem constant
  | Wildcard -- a type wildcard
  deriving (Eq, Ord, Show, Typeable, Data)

data TyVar = TyVar
  { tyvarFlavour    :: Flavour
  , tyvarName       :: Name
  , tyvarPrefix     :: Char -- used to generate names
  , tyvarConstraint :: Constraint
  } deriving (Eq, Ord, Show, Typeable, Data)

data MetaTv = MetaTv  -- can unify with any tau-type
  { metaUnique      :: Uniq
  , metaPrefix      :: Char -- used to generate names
  , metaConstraint  :: Constraint
  } deriving (Eq, Ord, Show, Typeable, Data)

-- | Type variable constraints
-- e.g. for types of kind row, labels the associated tyvar must lack
data Constraint
  = CNone
  | CRow  (Set Label)
  | CStar StarHierarchy
  deriving (Eq, Ord, Show, Typeable, Data)

-- | A simple hierarchy. i.e. Num has Ord and Eq, Ord has Eq.
data StarHierarchy
  = CEq
  | COrd
  | CNum
  deriving (Eq, Ord, Show, Typeable, Data)

-- | The type environment.
newtype TypeEnv = TypeEnv { unTypeEnv :: Map Name Sigma }
  deriving (Semigroup, Monoid)

insertTypeEnv :: Name -> Sigma -> TypeEnv -> TypeEnv
insertTypeEnv name ty (TypeEnv m) = TypeEnv $ M.insert name ty m

typeEnvToList :: TypeEnv -> [(Name, Sigma)]
typeEnvToList (TypeEnv m) = M.toList m

-- | Global map of type synonym definitions.
newtype Synonyms = Synonyms { unSynonym :: Map Name SynonymDecl }
  deriving (Semigroup, Monoid)

-- | A type synonym definition.
data SynonymDecl = SynonymDecl
    { synonymPos    :: Pos
    , synonymName   :: Name
    , synonymParams :: [TyVar]
    , synonymBody   :: Type
    } deriving (Show, Typeable, Data)

-- | Lookup and expand a type synonym.
-- Returns Nothing if the lookup or expansion failed.
lookupSynonym :: Name -> [Type] -> Synonyms -> Maybe Sigma
lookupSynonym name args (Synonyms m) = do
    SynonymDecl{..} <- M.lookup name m
    guard $ length synonymParams == length args
    return $ substTyVar synonymParams args synonymBody

-- | Used by the REPL.
deleteSynonym :: Name -> Synonyms -> Synonyms
deleteSynonym name (Synonyms m) =
    Synonyms $ M.delete name m

-- | Checks for duplicate synonym names and free variables.
insertSynonyms
    :: MonadError String m
    => [SynonymDecl]
    -> Synonyms
    -> m Synonyms
insertSynonyms ss (Synonyms m) =
    Synonyms <$> foldM f m ss
  where
    f m syn
        | Just syn' <- M.lookup (synonymName syn) m
        -- check that it's not a benign re-import of the same synonym
        , (fields syn /= fields syn') =
            throwError $ unwords
                [ "Duplicate synonyms with name"
                , "'" ++ synonymName syn ++ "'"
                , "at"
                , show syn --(synonymPos syn)
                , "and"
                , show syn' -- (synonymPos syn')
                ]
        | fvs <- ftv (synonymBody syn)
            S.\\ S.fromList (synonymParams syn)
        , not (S.null fvs) =
            throwError $ unwords
                [ "Free variables in type synonym definition:"
                , "'" ++ synonymName syn ++ "'"
                , "at"
                , show (synonymPos syn)
                ]
        | otherwise = return $ M.insert (synonymName syn) syn m

    -- strip positional annotations
    fields (SynonymDecl _ name vars body) = (name, vars, stripAnn body)

instance View TypeF Type where
  proj    = left . unFix
  inj  e  = Fix (e :*: K dummyPos)

-- | A useless source position.
dummyPos :: Pos
dummyPos = newPos "<unknown>" 1 1

instance View TypeF Type' where
  proj = unFix
  inj  = Fix

pattern TForAll vs t       <- (proj -> (TForAllF vs t)) where
  TForAll vs t = inj (TForAllF vs t)
pattern TVar v             <- (proj -> (TVarF v)) where
  TVar v = inj (TVarF v)
pattern TMetaVar v         <- (proj -> (TMetaVarF v)) where
  TMetaVar v = inj (TMetaVarF v)
pattern TSynonym v ts      <- (proj -> (TSynonymF v ts)) where
  TSynonym v ts = inj (TSynonymF v ts)
pattern TInt               <- (proj -> TIntF) where
  TInt = inj TIntF
pattern TDbl               <- (proj -> TDblF) where
  TDbl = inj TDblF
pattern TBool              <- (proj -> TBoolF) where
  TBool = inj TBoolF
pattern TChar              <- (proj -> TCharF) where
  TChar = inj TCharF
pattern TText              <- (proj -> TTextF) where
  TText = inj TTextF
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
  -- | Free type variables
  ftv   :: a -> Set TyVar

  -- | Meta type variables
  meta  :: a -> Set MetaTv

  -- | Replace meta type variables with types
  apply :: Subst -> a -> a

instance Types Type where
  ftv = cata alg . stripAnn where
    alg :: TypeF (Set TyVar) -> (Set TyVar)
    alg (TForAllF vs t) = t S.\\ S.fromList vs
    alg (TVarF v)       = S.singleton v
    alg e               = fold e

  meta = cata alg . stripAnn where
    alg :: TypeF (Set MetaTv) -> (Set MetaTv)
    alg (TMetaVarF v) = S.singleton v
    alg e             = fold e

  apply s t = cata alg t where
    alg :: (TypeF :*: K Pos) Type -> Type
    alg (TMetaVarF v :*: K p) =
        case IM.lookup (metaUnique v) (unSubst s) of
            Nothing -> Fix (TMetaVarF v :*: K p)
            Just t  -> apply s t -- TODO could this ever fail to terminate?
    alg e = Fix e

instance Types TypeEnv where
  ftv (TypeEnv env)  = ftv (M.elems env)
  meta (TypeEnv env) = meta (M.elems env)
  apply s (TypeEnv env) = TypeEnv (M.map (apply s) env)

instance Types a => Types [a] where
  ftv  = foldMap ftv
  meta = foldMap meta
  apply s = map (apply s)

-- | Get all the binders used in ForAlls in the type, so that
-- when quantifying an outer forall, we can avoid these inner ones.
tyVarBndrs :: Type -> Set TyVar
tyVarBndrs = cata alg . stripAnn where
    alg :: TypeF (Set TyVar) -> (Set TyVar)
    alg (TForAllF vs t) = t <> S.fromList vs
    alg (TFunF arg res) = arg <> res
    alg _               = S.empty

-- Use to instantiate TyVars
substTyVar :: [TyVar] -> [Type] -> Type -> Type
substTyVar tvs ts t = cata alg t m where
  alg :: (TypeF :*: K Pos) (Map Name Type -> Type)
      -> Map Name Type
      -> Type
  alg (TForAllF vs f :*: K p) m  =
      let m' = foldr M.delete m (map tyvarName vs)
      in Fix (TForAllF vs (f m') :*: K p)
  alg (TVarF v :*: K p) m =
        case M.lookup (tyvarName v) m of
            Nothing -> Fix (TVarF v :*: K p)
            Just t  -> t
  alg e m = Fix $ fmap ($m) e

  m = M.fromList $ (map tyvarName tvs) `zip` ts

newtype Subst = Subst { unSubst :: IntMap Type }
  deriving (Show)

nullSubst :: Subst
nullSubst = Subst IM.empty

infixr 0 |->
(|->) :: MetaTv -> Type -> Subst
(|->) v t = Subst $ IM.singleton (metaUnique v) t

isInSubst :: MetaTv -> Subst -> Bool
isInSubst v = IM.member (metaUnique v) . unSubst

removeFromSubst :: [MetaTv] -> Subst -> Subst
removeFromSubst vs (Subst m) =
    Subst $ foldr IM.delete m (map metaUnique vs)

-- | apply s1 and then s2
-- NB: order is important
composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = Subst $ (IM.map (apply s1) $ unSubst s2) `IM.union` unSubst s1

instance Semigroup Subst where
    (<>) = composeSubst

instance Monoid Subst where
    mempty = nullSubst

--  | decompose a row-type into its constituent parts
toList :: Type -> ([(Label, Type)], Maybe Type)
toList v@TVar{}           = ([], Just v)
toList v@TMetaVar{}       = ([], Just v)
toList TRowEmpty          = ([], Nothing)
toList (TRowExtend l t r) =
    let (ls, mv) = toList r
    in ((l, t):ls, mv)
toList t = error $ "Unexpected row type: " ++ show (ppType t)

extractMetaTv :: Type -> Maybe MetaTv
extractMetaTv (TMetaVar v) = Just v
extractMetaTv _            = Nothing

lacks :: [Label] -> Constraint
lacks = CRow . S.fromList

mkRowType :: Type -> [(Label, Type)] -> Type
mkRowType = foldr $ \(l, t@(getAnn -> pos)) r ->
    Fix (TRowExtendF l t r :*: K pos)

rowToMap :: Type -> Map Name Type
rowToMap (TRowExtend l t r) = M.insert l t (rowToMap r)
rowToMap TRowEmpty          = M.empty
rowToMap TVar{}             = M.empty -- default any row vars to empty row
rowToMap TMetaVar{}         = M.empty
rowToMap t                  = error $ "Unexpected row type: " ++ show (ppType t)


------------------------------------------------------------
-- Constraints

-- | True if the supplied type of kind Star satisfies the supplied constraint
satisfies :: Synonyms -> Type -> Constraint -> Bool
satisfies syns t c =
    case (infer t, c) of
        (CNone,    CNone)    -> True
        (CStar{},  CNone)    -> True
        (CNone,    CStar{})  -> False
        (CStar c1, CStar c2) -> c1 >= c2
        (c1, c2)  -> error $ "satisfies: kind mismatch: " ++ show (c1, c2)
  where
    infer :: Type -> Constraint
    infer (TForAll _ t)   = infer t
    infer (TVar     v)    = tyvarConstraint v
    infer (TMetaVar m)    = metaConstraint m
    infer (TSynonym n ts) =
        maybe CNone infer $ lookupSynonym n ts syns
    infer TInt            = CStar CNum
    infer TDbl            = CStar CNum
    infer TBool           = CStar COrd
    infer TChar           = CStar COrd
    infer TText           = CStar COrd
    infer TFun{}          = CNone
    infer (TList t)       = minC (CStar COrd) $ infer t
    infer (TRecord r)     = -- NB: unit supports equality
        maybe (CStar CEq) (minC (CStar CEq)) $ inferFromRow r
    infer (TVariant r)    = -- NB: void does not support equality
        maybe CNone (minC (CStar CEq)) $ inferFromRow r
    infer t = error $ "satisfies/infer: unexpected type: " ++ show t

    -- infer star constraints from row types
    inferFromRow :: Type -> Maybe Constraint
    inferFromRow TVar{}     = Nothing
    inferFromRow TMetaVar{} = Nothing
    inferFromRow (TSynonym n ts) =
        lookupSynonym n ts syns >>= inferFromRow
    inferFromRow TRowEmpty  = Nothing
    inferFromRow (TRowExtend _ t r) = Just $
        maybe (infer t) (minC (infer t)) $ inferFromRow r
    inferFromRow t =
        error $ "satisfies/inferFromRow: unexpected type: " ++ show t

    minC (CStar c1) (CStar c2) = CStar $ min c1 c2
    minC CNone      _          = CNone
    minC _          CNone      = CNone
    minC _          _          = error "minC: assertion failed"

-- | unions constraints
-- for kind Star: picks the most specific, i.e. max c1 c2
-- for kind Row: unions the sets of lacks labels
unionConstraints :: Constraint -> Constraint -> Constraint
unionConstraints CNone      c          = c
unionConstraints c          CNone      = c
unionConstraints (CRow s1)  (CRow s2)  = CRow  $ s1 `S.union` s2
unionConstraints (CStar c1) (CStar c2) = CStar $ max c1 c2
unionConstraints c1 c2  = error $ "unionConstraints: kind mismatch: " ++ show (c1, c2)


------------------------------------------------------------
-- Pretty-printing

type Precedence = Int

topPrec, arrPrec, tcPrec, atomicPrec :: Precedence
topPrec    = 0  -- Top-level precedence
arrPrec    = 1  -- Precedence of (a->b)
tcPrec     = 2  -- Precedence of (T a b)
atomicPrec = 3  -- Precedence of t

precType :: Type -> Precedence
precType (TForAll _ _)  = topPrec
precType (TFun _ _)     = arrPrec
precType (TSynonym _ _) = tcPrec
precType _              = atomicPrec

-- | Print with parens if precedence arg > precedence of type itself
ppType' :: Precedence -> Type -> Doc
ppType' p t
    | p >= precType t = parens (ppType t)
    | otherwise       = ppType t

ppType :: Type -> Doc
ppType (TForAll vs t)     = ppForAll (vs, t)
ppType (TVar v)           = text $ tyvarName v
ppType (TMetaVar v)       = "v" <> int (metaUnique v)
ppType (TSynonym n ts)
    | null ts             = text n
    | otherwise           = text n <+> hsep (map (ppType' tcPrec) ts)
ppType TInt               = "Int"
ppType TDbl               = "Double"
ppType TBool              = "Bool"
ppType TChar              = "Char"
ppType TText              = "Text"
ppType (TFun t s)         = ppType' arrPrec t <+> "->" <+> ppType' (arrPrec-1) s
ppType (TList a)          = brackets $ ppType a
ppType (TRecord r)        = braces $ ppRowType r
ppType (TVariant r)       = angles $ ppRowType r
ppType TRowEmpty          = "(||)"
ppType (TRowExtend l a r) = "(|" <> text l <> ":" <> ppType a <> "|" <> ppType r <> "|)"
ppType t = error $ "Unexpected type: " ++ show t

ppRowType :: Type -> Doc
ppRowType r = sepBy comma (map ppEntry ls)
           <> maybe mempty (ppRowTail ls) mv
  where
    (ls, mv)       = toList r
    ppRowTail [] v = ppType v
    ppRowTail _  v = mempty <+> "|" <+> ppType v
    ppEntry (l, t) = text l <+> ":" <+> ppType t

ppRowLabels :: Type -> Doc
ppRowLabels row =
    hcat $ map squotes (L.intersperse comma (map text . M.keys . rowToMap $ row))

ppForAll :: ([TyVar], Type) -> Doc
ppForAll (vars, t)
  | null vars = ppType' topPrec t
  | otherwise = "forall" <+> (hsep $ map (ppType . TVar) vars) <> dot
                         <>  (let cs = concatMap ppConstraint vars
                              in if null cs then mempty else space <> (parensList cs <+> "=>"))
                         <+> ppType' topPrec t
  where
    ppConstraint :: TyVar -> [Doc]
    ppConstraint v =
      case tyvarConstraint v of
        CNone      -> []
        CStar CEq  -> ["Eq"  <+> ppType (TVar v)]
        CStar COrd -> ["Ord" <+> ppType (TVar v)]
        CStar CNum -> ["Num" <+> ppType (TVar v)]
        CRow (S.toList -> ls)
            | null ls   -> []
            | otherwise -> [catBy "\\" $ ppType (TVar v) : map text ls]

ppPos :: Pos -> Doc
ppPos = text . show

ppStarConstraint :: StarHierarchy -> Doc
ppStarConstraint CEq  = "Eq"
ppStarConstraint COrd = "Ord"
ppStarConstraint CNum = "Num"
