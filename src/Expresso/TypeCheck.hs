{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

----------------------------------------------------------------------
-- Type inference and checking.
--
-- The type system implemented here is a bi-directional Damas-Milner system extended with
-- higher-rank polymorphism, type wildcards and polymorphic extensible (constrained) row types.
--
-- The algorithm is described in detail by the tutorial paper:
-- "Practical type inference for arbitrary-rank types" Peyton-Jones et al. 2011.
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
import Control.Monad.Except hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State hiding (mapM)
import Data.Monoid

import Expresso.Syntax
import Expresso.Type
import Expresso.Pretty
import Expresso.Utils

#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (mapM, concat)
import Data.Foldable
import Data.Traversable
#endif

data TIState = TIState
    { tiSupply :: Int
    , tiSubst  :: Subst
    }

type TI a = ExceptT String (ReaderT TypeEnv (State TIState)) a

runTI :: TI a -> TypeEnv -> TIState -> (Either String a, TIState)
runTI t tEnv tState = runState (runReaderT (runExceptT t) tEnv) tState

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
    annotate pos . _TMetaVar <$> newMetaTyVar c prefix

newMetaTyVar :: Constraint -> Char -> TI MetaTv
newMetaTyVar c prefix = do
  i <- fresh
  return $ MetaTv i prefix c

getEnvTypes :: TI [Sigma]
getEnvTypes = (M.elems . unTypeEnv <$> ask) >>= mapM substType

substType :: Type -> TI Type
substType t = do
  s <- gets tiSubst
  return $ apply s t

lookupVar :: Pos -> Name -> TI Sigma
lookupVar pos name = do
    TypeEnv env <- ask
    case M.lookup name env of
        Just s  -> return s
        Nothing -> throwError $ show $
            ppPos pos <+> ": unbound variable:" <+> text name

extendEnv :: M.Map Name Sigma -> TI a -> TI a
extendEnv binds = local (TypeEnv binds <>)

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
    s  = mconcat $ zipWith (|->) mvs (map _TVar tvs)
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
  let ts = map (annotate pos . _TMetaVar) tvs'
  s <- gets tiSubst
  return $ substTyVar tvs ts (apply s t)
instantiate _ t = return t

-- | Performs deep skolemisation, returning the
-- skolem constants and the skolemised type.
skolemise :: Pos -> Sigma -> TI ([TyVar], Rho)
skolemise pos (TForAll tvs t) = do
    sks1  <- mapM newSkolemTyVar tvs
    let sksTs = map (annotate pos . _TVar) sks1
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
mgu TInt TInt = return nullSubst
mgu TDbl TDbl = return nullSubst
mgu TBool TBool = return nullSubst
mgu TChar TChar = return nullSubst
mgu (TMaybe u) (TMaybe v) = mgu u v
mgu (TList u) (TList v) = mgu u v
mgu (TRecord row1) (TRecord row2) = mgu row1 row2
mgu (TVariant row1) (TVariant row2) = mgu row1 row2
mgu TRowEmpty TRowEmpty = return nullSubst
mgu row1@(TRowExtend label1 fieldTy1 rowTail1) row2@TRowExtend{} = do
  -- apply side-condition to ensure termination
  (fieldTy2, rowTail2, theta1) <- rewriteRow (getAnn row1) (getAnn row2) row2 label1
  case snd (rowToList rowTail1) >>= extractMetaTv of
    Just tv | isInSubst tv theta1 ->
                  throwError $ show (getAnn row1) ++ " : recursive row type"
    _ -> do
      theta2 <- mgu (apply theta1 fieldTy1) (apply theta1 fieldTy2)
      let s = theta2 <> theta1
      theta3 <- mgu (apply s rowTail1) (apply s rowTail2)
      return $ theta3 <> s
mgu t1 t2 = throwError $ show $ vcat
    [ "Types do not unify:"
    , ppPos (getAnn t1) <+> ":" <+> ppType t1
    , ppPos (getAnn t2) <+> ":" <+> ppType t2
    ]

-- | in order to unify two meta type variables, we must unify any constraints
unifyConstraints :: Pos -> MetaTv -> MetaTv -> TI Subst
unifyConstraints pos u v
  | u == v    = return nullSubst
  | otherwise =
      case (metaConstraint u, metaConstraint v) of
       (CNone, CNone) ->
           return $ u |-> annotate pos (_TMetaVar v)
       (c1, c2) -> do
           let prefix = metaPrefix v
           w <- newMetaVar pos (c1 `unionConstraints` c2) prefix
           return $ mconcat
               [ u |-> w
               , v |-> w
               ]

varBind :: Pos -> MetaTv -> Type -> TI Subst
varBind pos u t
  | u `S.member` meta t = throwError $ show $ vcat
        [ "Occur check fails:"
        , ppPos pos        <+> ppType (_TMetaVar u)
        , "occurs in"
        , ppPos (getAnn t) <+> ppType t
        ]
  | otherwise          =
        case metaConstraint u of
            CNone  -> return $ u |-> t
            CStar c
                | t `satisfies` metaConstraint u -> return $ u |-> t
                | otherwise ->
                         throwError $ show $ vcat
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
    (ls', mv)    = (S.fromList . map fst) *** (>>= extractMetaTv) $ rowToList t
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
      return (fieldTy', _TRowExtend label fieldTy rowTail', s)
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
    alg (ELam b e :*: K pos) Nothing = do -- TODO see Mu tCheckPats?
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
         throwError $ show $ vcat $
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
    unify ty (_TRecord $ mkRowType r $ zip xs tvs)
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
        throwError $ show $
            vcat [ ppPos pos <+> ": Subsumption check failed:"
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
tcDecl :: Pos -> Bind Name -> Exp -> TI TypeEnv
tcDecl pos b e = do
   t <- tcRho e Nothing
   binds <- tcBinds pos b (Just t) >>= mapM (inferSigma pos)
   extendEnv binds ask

tcPrim :: Pos -> Prim -> Type
tcPrim pos prim = annotate pos $ case prim of
  Int{}                  -> _TInt
  Dbl{}                  -> _TDbl
  Bool{}                 -> _TBool
  Char{}                 -> _TChar
  String{}               -> _TList _TChar
  Show                   ->
    -- use an Eq constraint, to prevent attempting to show lambdas
    let a = newTyVar (CStar CEq) 'a'
    in _TForAll [a] $ _TFun (_TVar a) (_TList _TChar)
  Trace                  ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun (_TFun (_TList _TChar) (_TVar a))
                                (_TVar a)
  ErrorPrim              ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun (_TList _TChar) (_TVar a)

  ArithPrim{}            ->
    binOp  $ newTyVar (CStar CNum) 'a'
  RelPrim{}              ->
    binOpB $ newTyVar (CStar COrd) 'a'

  Not                    -> _TFun _TBool _TBool
  And                    -> _TFun _TBool (_TFun _TBool _TBool)
  Or                     -> _TFun _TBool (_TFun _TBool _TBool)

  Eq                     -> binOpB $ newTyVar (CStar CEq) 'a'
  NEq                    -> binOpB $ newTyVar (CStar CEq) 'a'

  Double                 -> _TFun _TInt _TDbl
  Floor                  -> _TFun _TDbl _TInt
  Ceiling                -> _TFun _TDbl _TInt
  Abs                    ->
      unOp  $ newTyVar (CStar CNum) 'a'
  Neg                    ->
      unOp  $ newTyVar (CStar CNum) 'a'
  Mod                    ->
    _TFun _TInt (_TFun _TInt _TInt)
  FixPrim                ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun (_TFun (_TVar a) (_TVar a)) (_TVar a)
  FwdComp                ->   -- forward composition operator
    let a = newTyVar CNone 'a' -- (a -> b) -> (b -> c) -> a -> c
        b = newTyVar CNone 'b'
        c = newTyVar CNone 'c'
    in _TForAll [a,b,c] $ _TFun (_TFun (_TVar a) (_TVar b))
                                    (_TFun (_TFun (_TVar b) (_TVar c))
                                          (_TFun (_TVar a) (_TVar c)))
  BwdComp                ->   -- backward composition operator
    let a = newTyVar CNone 'a' -- (b -> c) -> (a -> b) -> a -> c
        b = newTyVar CNone 'b'
        c = newTyVar CNone 'c'
    in _TForAll [a,b,c] $ _TFun (_TFun (_TVar b) (_TVar c))
                                    (_TFun (_TFun (_TVar a) (_TVar b))
                                          (_TFun (_TVar a) (_TVar c)))
  JustPrim               ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun (_TVar a) (_TMaybe (_TVar a))
  NothingPrim            ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TMaybe (_TVar a)
  MaybePrim              ->
    let a = newTyVar CNone 'a'
        b = newTyVar CNone 'b'
    in _TForAll [a,b] $ _TFun (_TVar b)
                            (_TFun (_TFun (_TVar a) (_TVar b))
                                  (_TFun (_TMaybe (_TVar a))
                                        (_TVar b)))
  Cond                   ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun _TBool
                                (_TFun (_TVar a)
                                      (_TFun (_TVar a) (_TVar a)))
  ListEmpty              ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TList (_TVar a)
  ListCons               ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun (_TVar a)
                          (_TFun (_TList (_TVar a))
                                (_TList (_TVar a)))
  ListFoldr              ->
    let a = newTyVar CNone 'a'
        b = newTyVar CNone 'b'
    in _TForAll [a,b] $ _TFun (_TFun (_TVar a) (_TFun (_TVar b) (_TVar b)))
                            (_TFun (_TVar b)
                                  (_TFun (_TList (_TVar a))
                                        (_TVar b)))
  ListNull               ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun (_TList (_TVar a)) _TBool
  ListAppend             ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun (_TList (_TVar a))
                          (_TFun (_TList (_TVar a))
                                (_TList (_TVar a))) -- TODO
  RecordEmpty            -> _TRecord _TRowEmpty
  (RecordSelect label)   ->
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in _TForAll [a,r] $
        _TFun (_TRecord $ _TRowExtend label (_TVar a) (_TVar r)) (_TVar a)
  (RecordExtend label)   ->
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in _TForAll [a,r] $
        _TFun (_TVar a)
             (_TFun (_TRecord (_TVar r))
                   (_TRecord $ _TRowExtend label (_TVar a) (_TVar r)))
  (RecordRestrict label) ->
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in _TForAll [a,r] $
        _TFun (_TRecord $ _TRowExtend label (_TVar a) (_TVar r))
             (_TRecord (_TVar r))
  Absurd                 ->
    let a = newTyVar CNone 'a'
    in _TForAll [a] $ _TFun (_TVariant _TRowEmpty) (_TVar a)
  (VariantInject label)  ->  -- dual of record select
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in _TForAll [a, r] $
        _TFun (_TVar a)
             (_TVariant $ _TRowExtend label (_TVar a) (_TVar r))
           -- a -> <l:a|r>
  (VariantEmbed label)   ->  -- dual of record restrict
    let a = newTyVar CNone 'a'
        r = newTyVar (lacks [label]) 'r'
    in _TForAll [a, r] $
        _TFun (_TVariant (_TVar r))
             (_TVariant $ _TRowExtend label (_TVar a) (_TVar r))
           -- <r> -> <l:a|r>
  (VariantElim label)    ->
    let a = newTyVar CNone 'a'
        b = newTyVar CNone 'b'
        r = newTyVar (lacks [label]) 'r'
    in _TForAll [a, b, r] $
        _TFun (_TFun (_TVar a) (_TVar b))
             (_TFun (_TFun (_TVariant (_TVar r)) (_TVar b))
                   (_TFun (_TVariant $ _TRowExtend label (_TVar a) (_TVar r))
                         (_TVar b)))
                  --  (a -> b) -> (<r> -> b) -> <l:a|r> -> b

  where
    binOpB tv = _TForAll [tv] $ _TFun ty (_TFun ty _TBool)
      where ty = _TVar tv
    binOp tv  = _TForAll [tv] $ _TFun ty (_TFun ty ty)
      where ty = _TVar tv
    unOp tv   = _TForAll [tv] $ _TFun ty ty
      where ty = _TVar tv

typeCheck :: Exp -> TI Sigma
typeCheck e = tcRho e Nothing >>= inferSigma (getAnn e)
