{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fmax-pmcheck-iterations=10000000 #-}

-- |
-- Module      : Expresso.TypeCheck
-- Copyright   : (c) Tim Williams 2017-2019
-- License     : BSD3
--
-- Maintainer  : info@timphilipwilliams.com
-- Stability   : experimental
-- Portability : portable
--
-- Type inference and checking.
--
-- The type system implemented here is a bi-directional Damas-Milner system extended with
-- higher-rank polymorphism, type wildcards and polymorphic extensible (constrained) row types.
--
-- The algorithm is described in detail by the tutorial paper:
-- "Practical type inference for arbitrary-rank types" Peyton-Jones et al. 2011.
--
-- The row-types extension is based on ideas from the following papers:
-- * "A Polymorphic Type System for Extensible Records and Variants" B. R. Gaster and M. P. Jones, 1996.
-- * "Extensible records with scoped labels" D. Leijen, 2005.
--
module Expresso.TypeCheck (
      typeCheck
    , tcDecl
    , runTI
    , initTIState
    , TI
    , TIState
    ) where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Applicative ((<$>))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Expresso.Syntax
import Expresso.Type
import Expresso.Pretty
import Expresso.Utils

-- | Internal state of the inference engine.
data TIState = TIState
    { tiSupply :: Int
    , tiSubst  :: Subst
    }

data TIEnv = TIEnv
    { tiTypeEnv  :: TypeEnv
    , tiSynonyms :: Synonyms
    }

type TI a = ExceptT String (ReaderT TIEnv (State TIState)) a

-- | Type check the supplied expression.
typeCheck :: Exp -> TI Sigma
typeCheck e = tcRho e Nothing >>= inferSigma (getAnn e)

-- | Run the type inference monad.
runTI
    :: TI a
    -> TypeEnv
    -> Synonyms
    -> TIState
    -> (Either String a, TIState)
runTI t tEnv syns tState =
    runState (runReaderT (runExceptT t) (TIEnv tEnv syns)) tState

-- | Initial state of the inference engine.
initTIState :: TIState
initTIState = TIState { tiSupply = 0, tiSubst = mempty }

fresh :: TI Int
fresh = do
  s <- get
  let i = tiSupply s
  put s {tiSupply = i + 1 }
  return i

-- Used by tcPrim
newTyVar :: Constraint -> Char -> TyVar
newTyVar c prefix = TyVar Bound [prefix] prefix c

newSkolemTyVar :: TyVar -> TI TyVar
newSkolemTyVar (TyVar _ _ prefix c) = do
  i <- fresh
  let name = prefix : show i
  return $ TyVar Skolem name prefix c

newMetaVar :: Pos -> Constraint -> Char -> TI Type
newMetaVar pos c prefix =
    annotate pos . TMetaVar <$> newMetaTyVar c prefix

newMetaTyVar :: Constraint -> Char -> TI MetaTv
newMetaTyVar c prefix = do
  i <- fresh
  return $ MetaTv i prefix c

getEnvTypes :: TI [Sigma]
getEnvTypes =
    (M.elems . unTypeEnv <$> asks tiTypeEnv) >>= mapM substType

substType :: Type -> TI Type
substType t = do
  s <- gets tiSubst
  return $ apply s t

lookupVar :: Pos -> Name -> TI Sigma
lookupVar pos name = do
    TypeEnv env <- asks tiTypeEnv
    case M.lookup name env of
        Just s  -> return s
        Nothing -> throwError $ show $
            ppPos pos <+> ": unbound variable:" <+> text name

extendEnv :: M.Map Name Sigma -> TI a -> TI a
extendEnv binds =
    local $ \e -> e { tiTypeEnv = TypeEnv binds <> tiTypeEnv e }

-- | Quantify over the specified type variables (all flexible).
quantify :: Pos -> [MetaTv] -> Rho -> Sigma
quantify pos mvs0 t =
    withAnn pos $ TForAllF tvs t'
  where
     -- group by prefix and number sequentially each prefix
    (mvs, tvs) = unzip
               . concat
               . M.elems
               . M.mapWithKey mkSubsts
               . M.fromListWith (++)
               . map (metaPrefix &&& (:[]))
               $ mvs0
    s  = mconcat $ zipWith (|->) mvs (map TVar tvs)
    t' = apply s t

    -- avoid quantified type variables in use
    usedBndrs = map tyvarName $ S.toList $ tyVarBndrs t

    mkSubsts p mvs =
        zipWith mkSubst mvs (prefixBndrs L.\\ usedBndrs)
      where
        prefixBndrs = [p] : [ (p:show i) | i <- [(1::Integer)..]]
        mkSubst mv name =
            (mv, TyVar Bound name p (metaConstraint mv))

-- | Instantiate the topmost foralls of the argument type
-- with flexible type variables.
instantiate :: Pos -> Sigma -> TI Rho
instantiate pos (TForAll tvs t) = do
  tvs' <- mapM (\v -> newMetaTyVar (tyvarConstraint v) (tyvarPrefix v)) tvs
  let ts = map (annotate pos . TMetaVar) tvs'
  s <- gets tiSubst
  return $ substTyVar tvs ts (apply s t)
instantiate _ t = return t

-- | Performs deep skolemisation, returning the
-- skolem constants and the skolemised type.
skolemise :: Pos -> Sigma -> TI ([TyVar], Rho)
skolemise pos (TForAll tvs t) = do
    sks1  <- mapM newSkolemTyVar tvs
    let sksTs = map (annotate pos . TVar) sks1
    t <- substType t
    (sks2, t') <- skolemise pos $ substTyVar tvs sksTs t
    return (sks1 ++ sks2, t')
skolemise pos (TFun argT resT) = do
    (sks, resT') <- skolemise pos resT
    return (sks, withAnn pos (TFunF argT resT'))
skolemise _ t =
    return ([], t)

unify :: Type -> Type -> TI ()
unify t1 t2 = do
  s <- gets tiSubst
  u <- mgu (apply s t1) (apply s t2)
  modify (\st -> st { tiSubst = u <> tiSubst st })

mgu :: Type -> Type -> TI Subst
mgu (TFun l r) (TFun l' r') = do
  s1 <- mgu l l'
  s2 <- mgu (apply s1 r) (apply s1 r')
  return $ s2 <> s1
mgu (TMetaVar u) t@(TMetaVar v) = unifyConstraints (getAnn t) u v
mgu l@(TMetaVar v) t = varBind (getAnn l) v t
mgu t r@(TMetaVar v) = varBind (getAnn r) v t
mgu (TVar u) (TVar v)
    | u == v = return nullSubst
mgu t1@(TSynonym n1 ts1) t2@(TSynonym n2 ts2) -- no need to expand
    | n1 == n2  = mconcat <$> zipWithM mgu ts1 ts2
    | otherwise = throwError'
    [ "Type synonyms do not unify:"
    , ppPos (getAnn t1) <+> ":" <+> ppType t1
    , ppPos (getAnn t2) <+> ":" <+> ppType t2
    ]
mgu l@(TSynonym n1 ts1) t2 = do
    t1 <- expandSynonym (getAnn l) n1 ts1
    mgu t1 t2
mgu t1 r@(TSynonym n2 ts2) = do
    t2 <- expandSynonym (getAnn r) n2 ts2
    mgu t1 t2
mgu TInt TInt = return nullSubst
mgu TDbl TDbl = return nullSubst
mgu TBool TBool = return nullSubst
mgu TChar TChar = return nullSubst
mgu TText TText = return nullSubst
mgu (TList u) (TList v) = mgu u v
mgu (TRecord row1) (TRecord row2) = mgu row1 row2
mgu (TVariant row1) (TVariant row2) = mgu row1 row2
mgu TRowEmpty TRowEmpty = return nullSubst
mgu row1@TRowExtend{} row2@TRowEmpty = unifyRow row1 row2
mgu row1@TRowEmpty row2@TRowExtend{} = unifyRow row2 row1
mgu row1@TRowExtend{} row2@TRowExtend{} = unifyRow row1 row2
mgu t1 t2 = throwError'
    [ "Types do not unify:"
    , ppPos (getAnn t1) <+> ":" <+> ppType t1
    , ppPos (getAnn t2) <+> ":" <+> ppType t2
    ]

expandSynonym :: Pos -> Name -> [Type] -> TI Type
expandSynonym pos name args = do
    syns <- asks tiSynonyms
    case lookupSynonym name args syns of
        Just ty -> return ty
        Nothing -> throwError'
            [ "Could not expand type synonym:"
            , ppPos pos <+> ":" <+> ppType (TSynonym name args)
            ]

unifyRow :: Type -> Type -> TI Subst
unifyRow row1@TRowExtend{} row2@TRowEmpty = throwError' $
    [ ppPos (getAnn row1) <+> ": unexpected row label(s)"
      <+> hcat (L.intersperse comma (map text . M.keys . rowToMap $ row1))
    , "at" <+> ppPos (getAnn row2)
    ]
unifyRow row1@(TRowExtend label1 fieldTy1 rowTail1) row2@TRowExtend{} = do
  -- apply side-condition to ensure termination
  (fieldTy2, rowTail2, theta1) <- rewriteRow (getAnn row1) (getAnn row2) row2 label1
  case snd (toList rowTail1) >>= extractMetaTv of
    Just tv | isInSubst tv theta1 ->
                  throwError $ show (getAnn row1) ++ " : recursive row type"
    _ -> do
      theta2 <- mgu (apply theta1 fieldTy1) (apply theta1 fieldTy2)
      let s = theta2 <> theta1
      theta3 <- mgu (apply s rowTail1) (apply s rowTail2)
      return $ theta3 <> s
unifyRow t1 t2 = error $ "Assertion failed: " ++ show (t1, t2)

-- | in order to unify two meta type variables, we must unify any constraints
unifyConstraints :: Pos -> MetaTv -> MetaTv -> TI Subst
unifyConstraints pos u v
  | u == v    = return nullSubst
  | otherwise =
      case (metaConstraint u, metaConstraint v) of
       (CNone, CNone) ->
           return $ u |-> annotate pos (TMetaVar v)
       (c1, c2) -> do
           let prefix = metaPrefix v
           w <- newMetaVar pos (c1 `unionConstraints` c2) prefix
           return $ mconcat
               [ u |-> w
               , v |-> w
               ]

varBind :: Pos -> MetaTv -> Type -> TI Subst
varBind pos u t
  | u `S.member` meta t = throwError'
        [ "Occur check fails:"
        , ppPos pos        <+> ppType (TMetaVar u)
        , "occurs in"
        , ppPos (getAnn t) <+> ppType t
        ]
  | otherwise          = do
        syns <- asks tiSynonyms
        case metaConstraint u of
            CNone  -> return $ u |-> t
            CStar c
                | satisfies syns t (metaConstraint u) ->
                      return $ u |-> t
                | otherwise ->
                      throwError'
                          [ "The type:"
                          , ppPos (getAnn t) <+> ":" <+> ppType t
                          , "does not satisfy the constraint:"
                          , ppPos pos <+> ":" <+> ppStarConstraint c
                          ]
            CRow{} -> varBindRow (getAnn t) u t

-- | bind the row tyvar to the row type, as long as the row type does not
-- contain the labels in the tyvar lacks constraint; and propagate these
-- label constraints to the row variable in the row tail, if there is one.
varBindRow :: Pos -> MetaTv -> Type -> TI Subst
varBindRow pos u t
  = case S.toList (ls `S.intersection` ls') of
      [] | Nothing <- mv -> return s1
         | Just r1 <- mv -> do
             let c = ls `S.union` (labelsFrom r1)
             r2 <- newMetaVar pos (CRow c) 'r'
             let s2 = r1 |-> r2
             return $ s1 <> s2
      labels             -> throwError $ show $
                                ppPos pos <+> ": repeated label(s):"
                                          <+> sepBy comma (map text labels)
  where
    ls           = labelsFrom u
    (ls', mv)    = (S.fromList . map fst) *** (>>= extractMetaTv) $ toList t
    s1           = u |-> t
    labelsFrom v = case metaConstraint v of
        CRow s -> s
        _      -> S.empty

rewriteRow :: Pos -> Pos -> Type -> Label -> TI (Type, Type, Subst)
rewriteRow pos1 pos2 (Fix (TRowEmptyF :*: _)) newLabel =
  throwError $ show $
      ppPos pos1 <+> ": label" <+> text newLabel <+> "cannot be inserted into row type introduced at" <+> ppPos pos2
rewriteRow pos1 pos2 (Fix (TRowExtendF label fieldTy rowTail :*: K pos)) newLabel
  | newLabel == label     =
      -- nothing to do
      return (fieldTy, rowTail, nullSubst)
  | TVar v <- rowTail, tyvarFlavour v == Skolem =
      throwError $ show $ vcat $
          [ ppPos pos1 <+> ": Type not polymorphic enough:"
          , ppPos pos2
          ]
  | TMetaVar alpha <- rowTail = do
      beta  <- newMetaVar pos (lacks [newLabel]) 'r'
      gamma <- newMetaVar pos CNone 'a'
      s      <- varBindRow pos alpha
                    $ withAnn pos
                    $ TRowExtendF newLabel gamma beta
      return ( gamma
             , apply s $ withAnn pos $ TRowExtendF label fieldTy beta
             , s
             )
  | otherwise   = do
      (fieldTy', rowTail', s) <- rewriteRow pos1 pos2 rowTail newLabel
      return (fieldTy', TRowExtend label fieldTy rowTail', s)
rewriteRow _ _ ty _ = error $ "Unexpected type: " ++ show ty

-- | type-checking and inference
tcRho :: Exp -> Maybe Rho -> TI Type
tcRho = cata alg
  where
    alg :: (ExpF Name Bind Type :*: K Pos) (Maybe Rho -> TI Type)
        -> Maybe Rho
        -> TI Type
    alg (EVar n :*: K pos) mty = do
        sigma <- lookupVar pos n
        instSigma pos sigma mty
    alg (EPrim prim :*: K pos) mty = do
        let sigma = tcPrim pos prim
        instSigma pos sigma mty
    alg (ELam b e :*: K pos) Nothing = do
        varT <- newMetaVar pos CNone 'a'
        binds <- tcBinds pos b $ Just varT
        extendEnv binds $ do
            resT <- e Nothing
            return $ withAnn pos $ TFunF varT resT
    alg (ELam b e :*: K pos) (Just ty) = do
        (varT, bodyT) <- unifyFun pos ty
        binds <- tcBinds pos b $ Just varT
        extendEnv binds $
            e (Just bodyT)
    alg (EAnnLam b argT e :*: K pos) Nothing = do
        argT  <- instWildcards argT
        binds <- tcBinds pos b $ Just argT
        extendEnv binds $ do
            resT <- e Nothing
            return $ withAnn pos $ TFunF argT resT
    alg (EAnnLam b varT e :*: K pos) (Just ty) = do
        varT  <- instWildcards varT
        (argT, bodyT) <- unifyFun pos ty
        subsCheck pos argT varT
        binds <- tcBinds pos b $ Just varT
        extendEnv binds $
            e (Just bodyT)
    alg (EApp e1 e2 :*: K pos) mty = do
        funT <- e1 Nothing
        (argT, resT) <- unifyFun pos funT
        checkSigma pos e2 argT
        instSigma pos resT mty
    alg (ELet b e1 e2 :*: K pos) mty = do
        t1 <- e1 Nothing
        binds <- tcBinds pos b (Just t1) >>= mapM (inferSigma pos)
        extendEnv binds $
            e2 mty
    alg (EAnnLet b varT e1 e2 :*: K pos) mty = do
        varT  <- instWildcards varT
        t1 <- e1 Nothing
        subsCheck pos t1 varT
        binds <- tcBinds pos b $ Just varT
        extendEnv binds $
            e2 mty
    alg (EAnn e annT :*: K pos) mty = do
        annT  <- instWildcards annT
        checkSigma pos e annT
        instSigma pos annT mty

inferSigma :: Pos -> Rho -> TI Sigma
inferSigma pos rho = do
    exp_ty  <- substType rho
    env_tys <- getEnvTypes
    let env_tvs    = meta env_tys
        res_tvs    = meta [exp_ty]
        forall_tvs = S.toList $ res_tvs S.\\ env_tvs
    return $ quantify pos forall_tvs exp_ty

checkSigma :: Pos -> (Maybe Rho -> TI Rho) -> Sigma -> TI ()
checkSigma pos e sigma = do
    (skol_tvs, rho) <- skolemise pos sigma
    void $ e (Just rho)
    env_tys <- getEnvTypes
    let esc_tvs = ftv (sigma : env_tys)
        bad_tvs = filter (`S.member` esc_tvs) skol_tvs
    unless (null bad_tvs) $
         throwError'
              [ ppPos pos <+> ": Type not polymorphic enough:"
              , parensList (map (text . tyvarName) bad_tvs)
              ]

instSigma :: Pos -> Sigma -> Maybe Rho -> TI Type
instSigma pos t1 Nothing   = instantiate pos t1
instSigma pos t1 (Just t2) = subsCheckRho pos t1 t2 >> return t2

-- NOTE: Currently we support only simple unamed type wildcards.
-- Each one is distinct and we generate fresh meta vars for them.
instWildcards :: Rho -> TI Rho
instWildcards = cataM alg
  where
    alg :: (TypeF :*: K Pos) Type -> TI Type
    alg (TVarF v :*: K pos) | tyvarFlavour v == Wildcard = do
          mv <- newMetaTyVar (tyvarConstraint v) 't'
          return $ withAnn pos (TMetaVarF mv)
    alg e = return $ Fix e

tcBinds :: Pos -> Bind Name -> Maybe Rho -> TI (M.Map Name Type)
tcBinds pos arg           Nothing   =
    newMetaVar pos CNone 'a' >>= tcBinds pos arg . Just
tcBinds _   (Arg x)       (Just ty) =
    return $ M.singleton x ty
tcBinds pos (RecArg xs)   (Just ty) = do
    tvs <- mapM (const $ newMetaVar pos CNone 'l') xs
    r   <- newMetaVar pos (lacks xs) 'r' -- implicit tail
    unify ty (TRecord $ mkRowType r $ zip xs tvs)
    return $ M.fromList $ zip xs tvs
tcBinds pos RecWildcard   (Just ty) = do
    s <- gets tiSubst
    case apply s ty of
        TRecord r -> return $ rowToMap r
        _         ->
            throwError $ show $
                ppPos pos <+> ": record wildcard cannot bind to type:" <+> ppType ty


subsCheck :: Pos -> Sigma -> Sigma -> TI ()
subsCheck pos sigma1 sigma2 = do
    (skol_tvs, rho2) <- skolemise pos sigma2
    subsCheckRho pos sigma1 rho2
    let esc_tvs = ftv [sigma1, sigma2]
        bad_tvs = filter (`S.member` esc_tvs) skol_tvs
    unless (null bad_tvs) $
        throwError'
            [ ppPos pos <+> ": Subsumption check failed:"
            , indent 2 (ppType sigma1)
            , text "is not as polymorphic as"
            , indent 2 (ppType sigma2)
            ]

subsCheckRho :: Pos -> Sigma -> Rho -> TI ()
subsCheckRho pos sigma1@(TForAll _ _) rho2 = do
    rho1 <- instantiate pos sigma1
    subsCheckRho pos rho1 rho2
subsCheckRho pos rho1 (TFun a2 r2) = do
    (a1, r1) <- unifyFun pos rho1
    subsCheckFun pos a1 r1 a2 r2
subsCheckRho pos (TFun a1 r1) rho2 = do
    (a2, r2) <- unifyFun pos rho2
    subsCheckFun pos a1 r1 a2 r2
subsCheckRho _   tau1 tau2 =
    unify tau1 tau2

subsCheckFun :: Pos -> Sigma -> Rho -> Sigma -> Rho -> TI ()
subsCheckFun pos a1 r1 a2 r2 = do
    subsCheck pos a2 a1
    subsCheckRho pos r1 r2

unifyFun :: Pos -> Rho -> TI (Sigma, Rho)
unifyFun _   (TFun argT resT) = return (argT, resT)
unifyFun pos tau = do
    argT <- newMetaVar pos CNone 'a'
    resT <- newMetaVar pos CNone 'b'
    unify tau (withAnn pos $ TFunF argT resT)
    return (argT, resT)

-- used by the Repl
tcDecl :: Pos -> Bind Name -> Maybe Type -> Exp -> TI TypeEnv
tcDecl pos b Nothing e = do
   t <- tcRho e Nothing
   binds <- tcBinds pos b (Just t) >>= mapM (inferSigma pos)
   extendEnv binds (asks tiTypeEnv)
tcDecl pos b (Just varT) e = do
   varT  <- instWildcards varT
   t <- tcRho e Nothing
   subsCheck pos t varT
   binds <- tcBinds pos b $ Just varT
   extendEnv binds (asks tiTypeEnv)

tcPrim :: Pos -> Prim -> Type
tcPrim pos prim = annotate pos $ case prim of
  Int{}                  -> TInt
  Dbl{}                  -> TDbl
  Bool{}                 -> TBool
  Char{}                 -> TChar
  Text{}                 -> TText
  Show                   ->
    -- use an Eq constraint, to prevent attempting to show lambdas
    let a = newTyVar (CStar CEq) 'a'
    in TForAll [a] $ TFun (TVar a) TText
  Trace                  ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TFun (TFun TText (TVar a))
                          (TVar a)
  ErrorPrim              ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TFun TText (TVar a)

  ArithPrim{}            ->
    binOp  $ newTyVar (CStar CNum) 'a'
  RelPrim{}              ->
    binOpB $ newTyVar (CStar COrd) 'a'

  Not                    -> TFun TBool TBool
  And                    -> TFun TBool (TFun TBool TBool)
  Or                     -> TFun TBool (TFun TBool TBool)

  Eq                     -> binOpB $ newTyVar (CStar CEq) 'a'
  NEq                    -> binOpB $ newTyVar (CStar CEq) 'a'

  Double                 -> TFun TInt TDbl
  Floor                  -> TFun TDbl TInt
  Ceiling                -> TFun TDbl TInt
  Abs                    ->
      unOp  $ newTyVar (CStar CNum) 'a'
  Neg                    ->
      unOp  $ newTyVar (CStar CNum) 'a'
  Mod                    ->
    TFun TInt (TFun TInt TInt)
  FixPrim                ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TFun (TFun (TVar a) (TVar a)) (TVar a)
  FwdComp                ->   -- forward composition operator
    let a = newTyVar CNone 'a' -- (a -> b) -> (b -> c) -> a -> c
        b = newTyVar CNone 'b'
        c = newTyVar CNone 'c'
    in TForAll [a,b,c] $ TFun (TFun (TVar a) (TVar b))
                                    (TFun (TFun (TVar b) (TVar c))
                                          (TFun (TVar a) (TVar c)))
  BwdComp                ->   -- backward composition operator
    let a = newTyVar CNone 'a' -- (b -> c) -> (a -> b) -> a -> c
        b = newTyVar CNone 'b'
        c = newTyVar CNone 'c'
    in TForAll [a,b,c] $ TFun (TFun (TVar b) (TVar c))
                                    (TFun (TFun (TVar a) (TVar b))
                                          (TFun (TVar a) (TVar c)))
  Pack                   -> TFun (TList TChar) TText
  Unpack                 -> TFun TText (TList TChar)
  TextAppend             -> TFun TText (TFun TText TText)
  Cond                   ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TFun TBool
                                (TFun (TVar a)
                                      (TFun (TVar a) (TVar a)))
  ListEmpty              ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TList (TVar a)
  ListCons               ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TFun (TVar a)
                          (TFun (TList (TVar a))
                                (TList (TVar a)))
  ListFoldr              ->
    let a = newTyVar CNone 'a'
        b = newTyVar CNone 'b'
    in TForAll [a,b] $ TFun (TFun (TVar a) (TFun (TVar b) (TVar b)))
                            (TFun (TVar b)
                                  (TFun (TList (TVar a))
                                        (TVar b)))
  ListNull               ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TFun (TList (TVar a)) TBool
  ListAppend             ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TFun (TList (TVar a))
                          (TFun (TList (TVar a))
                                (TList (TVar a))) -- TODO
  RecordEmpty            -> TRecord TRowEmpty
  (RecordSelect label)   ->
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in TForAll [a,r] $
        TFun (TRecord $ TRowExtend label (TVar a) (TVar r)) (TVar a)
  (RecordExtend label)   ->
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in TForAll [a,r] $
        TFun (TVar a)
             (TFun (TRecord (TVar r))
                   (TRecord $ TRowExtend label (TVar a) (TVar r)))
  (RecordRestrict label) ->
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in TForAll [a,r] $
        TFun (TRecord $ TRowExtend label (TVar a) (TVar r))
             (TRecord (TVar r))
  Absurd                 ->
    let a = newTyVar CNone 'a'
    in TForAll [a] $ TFun (TVariant TRowEmpty) (TVar a)
  (VariantInject label)  ->  -- dual of record select
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in TForAll [a, r] $
        TFun (TVar a)
             (TVariant $ TRowExtend label (TVar a) (TVar r))
           -- a -> <l:a|r>
  (VariantEmbed label)   ->  -- dual of record restrict
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in TForAll [a, r] $
        TFun (TVariant (TVar r))
             (TVariant $ TRowExtend label (TVar a) (TVar r))
           -- <r> -> <l:a|r>
  (VariantElim label)    ->
    let a = newTyVar CNone 'a'
        b = newTyVar CNone 'b'
        r = newTyVar (lacks [label]) 'r'
    in TForAll [a, b, r] $
        TFun (TFun (TVar a) (TVar b))
             (TFun (TFun (TVariant (TVar r)) (TVar b))
                   (TFun (TVariant $ TRowExtend label (TVar a) (TVar r))
                         (TVar b)))
                  --  (a -> b) -> (<r> -> b) -> <l:a|r> -> b

  where
    binOpB tv = TForAll [tv] $ TFun ty (TFun ty TBool)
      where ty = TVar tv
    binOp tv  = TForAll [tv] $ TFun ty (TFun ty ty)
      where ty = TVar tv
    unOp tv   = TForAll [tv] $ TFun ty ty
      where ty = TVar tv

throwError' :: [Doc] -> TI a
throwError' = throwError . show . vcat
