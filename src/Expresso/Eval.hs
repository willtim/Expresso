{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- For the anti-recursion stuff
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}

------------------------------------------------------------
--
-- A lazy evaluator.
--
-- The front-end syntax is simple, so we evaluate it directly.
--
module Expresso.Eval(
    eval
  , runEvalM
  , Env
  , EvalM
  , Value(..)
  , ppValue
  , ppValue'
  , force
  , mkThunk
  , bind
  -- * Foreign
  , typeOf
  , toValue
  , fromValue
  , HasType(..)
  , FromValue(..)
  , ToValue(..)
)
where

import Control.Monad.Except hiding (mapM)
import Control.Applicative
import Data.Foldable (foldrM)
import Data.HashMap.Strict (HashMap)
import Data.Coerce
import Data.Maybe
import Data.Monoid
import Data.Ord
import qualified Data.HashMap.Strict as HashMap
import qualified Data.List as List
import Control.Monad.ST
import Data.STRef
import Data.Void
import Data.Functor.Identity
import Data.Proxy
import qualified GHC.Generics as G
import GHC.TypeLits


import Expresso.Syntax
import Expresso.Type
import Expresso.Pretty
import Expresso.Utils (cata, (:*:)(..), K(..))
import qualified Expresso.Parser as Parser

#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (mapM, concat, elem, and)
import Data.Foldable
import Data.Traversable
#endif


import Debug.Trace

-- call-by-need environment
-- A HashMap makes it easy to support record wildcards
type Env = HashMap Name Thunk

newtype EvalM a = EvalM { runEvalT :: ExceptT String Identity a }
deriving instance Functor EvalM
deriving instance Applicative EvalM
deriving instance Monad EvalM
deriving instance MonadError String EvalM

newtype Thunk = Thunk { force_ :: EvalM Value }

type ApplicativeMonadError e f = (Applicative f, MonadError e f)

class ApplicativeMonadError String f => MonadEval f where
  force :: Thunk -> f Value
instance MonadEval EvalM where
  force = force_

instance Show Thunk where
    show _ = "<Thunk>"

mkThunk :: EvalM Value -> EvalM Thunk
mkThunk = return . Thunk
-- mkThunk (EvalM ev) = EvalM $ do
--   ref <- lift $ newSTRef Nothing
--   return $ Thunk $ EvalM $ do
--       mv <- lift $ readSTRef ref
--       case mv of
--           Nothing -> do
--               v <- ev
--               lift $ writeSTRef ref (Just v)
--               return v
--           Just v  -> return v

data Value
  = VLam     !(Thunk -> EvalM Value)
  | VInt     !Integer
  | VDbl     !Double
  | VBool    !Bool
  | VChar    !Char
  {- | VString  !String  -- an optimisation -}
  | VMaybe   !(Maybe Value)
  | VList    ![Value] -- lists are strict
  | VRecord  !(HashMap Label Thunk) -- field order no defined
  | VVariant !Label !Thunk

{- applyV :: Value -> Value -> EvalM Value -}
{- applyV (VLam f) x = f (valueToThunk x) -}
  {- where -}
valueToThunk :: Value -> Thunk
valueToThunk = Thunk . pure
{- applyV f x = throwError $ "Not a function: " -- TODO ++ show f -}

-- | This does *not* evaluate deeply
ppValue :: Value -> Doc
ppValue (VLam  _)   = "<Lambda>"
ppValue (VInt  i)   = integer i
ppValue (VDbl  d)   = double d
ppValue (VBool b)   = if b then "True" else "False"
ppValue (VChar c)   = text $ c : []
ppValue (VMaybe mx) = maybe "Nothing" (\v -> "Just" <+> ppParensValue v) mx
{- ppValue (VString s) = string (show s) -}
ppValue (VList xs)
    | Just str <- mapM extractChar xs = string $ show str
    | otherwise     = bracketsList $ map ppValue xs
ppValue (VRecord m) = bracesList $ map ppEntry $ HashMap.keys m
  where
    ppEntry l = text l <+> "=" <+> "<Thunk>"
ppValue (VVariant l _) = text l <+> "<Thunk>"

ppParensValue :: Value -> Doc
ppParensValue v =
    case v of
        VMaybe{}   -> parens $ ppValue v
        VVariant{} -> parens $ ppValue v
        _          -> ppValue v

-- | This evaluates deeply
ppValue' :: Value -> EvalM Doc
ppValue' (VRecord m) = (bracesList . map ppEntry . HashMap.toList)
                           <$> mapM (force >=> ppValue') m
  where
    ppEntry (l, v) = text l <+> text "=" <+> v
ppValue' (VVariant l t) = (text l <+>) <$> (force >=> ppParensValue') t
ppValue' v = return $ ppValue v

ppParensValue' :: Value -> EvalM Doc
ppParensValue' v =
    case v of
        VMaybe{}   -> parens <$> ppValue' v
        VVariant{} -> parens <$> ppValue' v
        _          -> ppValue' v

extractChar :: Value -> Maybe Char
extractChar (VChar c) = Just c
extractChar _ = Nothing

runEvalM :: EvalM a -> IO (Either String a)
runEvalM = pure . runEvalM'

runEvalM' :: EvalM a -> Either String a
runEvalM' = runIdentity . runExceptT . runEvalT


eval :: Env -> Exp -> EvalM Value
eval env e = cata alg e env
  where
    alg :: (ExpF Name Bind Type :*: K Pos) (Env -> EvalM Value)
        -> Env
        -> EvalM Value
    alg (EVar v :*: _)         env = lookupValue env v >>= force
    alg (EApp f x :*: K pos)   env = do
        f' <- f env
        x' <- mkThunk (x env)
        evalApp pos f' x'
    alg (ELam b e1 :*: _  )    env = evalLam env b e1
    alg (EAnnLam b _ e1 :*: _) env = evalLam env b e1
    alg (ELet b e1 e2 :*: _)   env = do
        t    <- mkThunk $ e1 env
        env' <- bind env b t
        e2 env'
    alg (EPrim p :*: K pos)    _   = return $ evalPrim pos p
    alg (EAnn e _ :*: _)       env = e env

evalLam :: Env -> Bind Name -> (Env -> EvalM Value) -> EvalM Value
evalLam env b e = return $ VLam $ \x ->
    bind env b x >>= e

evalApp :: Pos -> Value -> Thunk -> EvalM Value
evalApp _   (VLam f)   t  = f t
evalApp pos fv         _  =
    throwError $ show pos ++ " : Expected a function, but got: " ++
                 show (ppValue fv)

evalPrim :: Pos -> Prim -> Value
evalPrim pos p = case p of
    Int i         -> VInt i
    Dbl d         -> VDbl d
    Bool b        -> VBool b
    Char c        -> VChar c
    {- String s      -> VString s -}
    String s      -> VList (fmap VChar s)
    Show          -> mkStrictLam $ \v -> string . show <$> ppValue' v
      where
        {- string = VString -}
        string = VList . fmap VChar
    -- Trace
    ErrorPrim     -> VLam $ \s -> do
{- <<<<<<< HEAD -}
        msg <- fromValue' s
        throwError $ "error (" ++ show pos ++ "):" ++ msg
{- ======= -}
        {- msg <- proj' s -}
        {- throwError $ "error (" ++ show pos ++ "): " ++ msg -}
{- >>>>>>> tim/master -}

    ArithPrim Add -> mkStrictLam2 $ numOp pos (+)
    ArithPrim Sub -> mkStrictLam2 $ numOp pos (-)
    ArithPrim Mul -> mkStrictLam2 $ numOp pos (*)
    ArithPrim Div -> mkStrictLam2 $ \v1 v2 ->
        case (v1, v2) of
            (VInt x, VInt y) -> return $ VInt $ x `div` y
            (VDbl x, VDbl y) -> return $ VDbl $ x / y
            _                -> failOnValues pos [v1, v2]

    RelPrim RGT   -> mkStrictLam2 $ \v1 v2 ->
        (VBool . (==GT)) <$> compareValues pos v1 v2

    RelPrim RGTE  -> mkStrictLam2 $ \v1 v2 ->
        (VBool . (`elem` [GT, EQ])) <$> compareValues pos v1 v2

    RelPrim RLT   -> mkStrictLam2 $ \v1 v2 ->
        (VBool . (==LT)) <$> compareValues pos v1 v2

    RelPrim RLTE  -> mkStrictLam2 $ \v1 v2 ->
        (VBool . (`elem` [LT, EQ])) <$> compareValues pos v1 v2

    Eq            -> mkStrictLam2 $ \v1 v2 ->
        VBool <$> equalValues pos v1 v2

    NEq           -> mkStrictLam2 $ \v1 v2 ->
        (VBool . not) <$> equalValues pos v1 v2

    Not           -> VLam $ \v -> VBool <$> fromValue' v
    And           -> VLam $ \v1 -> return $ VLam $ \v2 ->
        VBool <$> ((&&) <$> fromValue' v1 <*> fromValue' v2)

    Or            -> VLam $ \v1 -> return $ VLam $ \v2 ->
        VBool <$> ((||) <$> fromValue' v1 <*> fromValue' v2)

    Double        -> mkStrictLam $ \v ->
        case v of
            VInt i -> return $ VDbl $ fromInteger i
            _      -> failOnValues pos [v]
    Floor         -> mkStrictLam $ \v ->
        case v of
            VDbl d -> return $ VInt $ floor d
            _      -> failOnValues pos [v]
    Ceiling       -> mkStrictLam $ \v ->
        case v of
            VDbl d -> return $ VInt $ ceiling d
            _      -> failOnValues pos [v]

    Neg           -> mkStrictLam $ \v ->
        case v of
            VInt i -> return $ VInt $ negate i
            VDbl d -> return $ VDbl $ negate d
            _      -> failOnValues pos [v]

    Mod           -> mkStrictLam $ \v1 -> return $ mkStrictLam $ \v2 ->
        case (v1, v2) of
            (VInt x, VInt y) -> return $ VInt $ x `mod` y
            _                -> failOnValues pos [v1, v2]

    Cond     -> VLam $ \c -> return $ VLam $ \t -> return $ VLam $ \f ->
        fromValue' c >>= \c -> if c then force t else force f
    FixPrim       -> mkStrictLam $ \f -> fix (evalApp pos f <=< mkThunk)

    -- We cannot yet define operators like this in the language
    FwdComp       -> mkStrictLam2 $ \f g ->
        return $ VLam $ \x ->
            mkThunk (evalApp pos f x) >>= evalApp pos g
    BwdComp    -> mkStrictLam2 $ \f g ->
        return $ VLam $ \x ->
            mkThunk (evalApp pos g x) >>= evalApp pos f

    JustPrim      -> mkStrictLam $ \v -> return $ VMaybe (Just v)
    NothingPrim   -> VMaybe Nothing
    MaybePrim     -> VLam $ \x -> return $ mkStrictLam2 $ \f v ->
        case v of
            VMaybe (Just v') -> evalApp pos f (Thunk $ return v')
            VMaybe Nothing   -> force x
            _                -> failOnValues pos [v]

    ListEmpty     -> VList []
    ListNull      -> VLam $ \xs ->
        (VBool . (null :: [Value] -> Bool)) <$> (force >=> fromValueL return) xs
    ListCons      -> VLam $ \x -> return $ VLam $ \xs ->
        VList <$> ((:) <$> force x <*> (force >=> fromValueL return) xs)
    ListAppend    -> VLam $ \xs -> return $ VLam $ \ys ->
        VList <$> ((++) <$> (force >=> fromValueL return) xs <*> (force >=> fromValueL return) ys)
    ListFoldr     -> mkStrictLam $ \f ->
        return $ VLam $ \z -> return $ VLam $ \xs -> do
        let g a b = do g' <- evalApp pos f (Thunk $ return a)
                       evalApp pos g' (Thunk $ return b)
        z'  <- force z
        xs' <- (force >=> fromValueL return) xs :: EvalM [Value]
        foldrM g z' xs'
    RecordExtend l   -> VLam $ \v -> return $ VLam $ \r ->
        (VRecord . HashMap.insert l v) <$> (force >=> fromValueRTh) r
    RecordRestrict l -> VLam $ \r ->
        (VRecord . HashMap.delete l) <$> (force >=> fromValueRTh) r
    RecordSelect l   -> VLam $ \r -> do
        r' <- (force >=> fromValueRTh) r
        let err = throwError $ show pos ++ " : " ++ l ++ " not found"
        maybe err force (HashMap.lookup l r')
    RecordEmpty -> VRecord mempty
    VariantInject l  -> VLam $ \v ->
        return $ VVariant l v
    VariantEmbed _   -> VLam force
    VariantElim l    -> mkStrictLam $ \f -> return $ mkStrictLam2 $ \k s -> do
        case s of
            VVariant l' t | l==l'     -> evalApp pos f t
                          | otherwise -> evalApp pos k (Thunk $ return s)
            v -> throwError $ show pos ++ " : Expected a variant, but got: " ++
                              show (ppValue v)
    Absurd -> VLam $ \v -> force v >> throwError "The impossible happened!"
    p -> error $ show pos ++ " : Unsupported Prim: " ++ show p


-- non-strict bind
bind :: Env -> Bind Name -> Thunk -> EvalM Env
bind env b t = case b of
    Arg n -> return $ HashMap.insert n t env
    _     -> bind' env b t

-- strict bind
bind' :: Env -> Bind Name -> Thunk -> EvalM Env
bind' env b t = do
  v <- force t
  case (b, v) of
    (Arg n, _)               ->
        return $ HashMap.insert n (Thunk $ return v) env
    (RecArg ns, VRecord m) | Just vs <- mapM (\n -> HashMap.lookup n m) ns ->
        return $ env <> (HashMap.fromList $ zip ns vs)
    (RecWildcard, VRecord m) ->
        return $ env <> m
    _ -> throwError $ "Cannot bind the pair: " ++ show b ++ " = " ++ show (ppValue v)

lookupValue :: Env -> Name -> EvalM Thunk
lookupValue env n = maybe err return $ HashMap.lookup n env
  where
    err = throwError $ "Not found: " ++ show n

failOnValues :: Pos -> [Value] -> EvalM a
failOnValues pos vs = throwError $ show pos ++ " : Unexpected value(s) : " ++
                                   show (parensList (map ppValue vs))

mkStrictLam :: (Value -> EvalM Value) -> Value
mkStrictLam f = VLam $ \x -> force x >>= f

mkStrictLam2 :: (Value -> Value -> EvalM Value) -> Value
mkStrictLam2 f = mkStrictLam $ \v -> return $ mkStrictLam $ f v

fromValue' :: (MonadEval f, FromValue a) => Thunk -> f a
fromValue' = force >=> fromValue

numOp :: Pos -> (forall a. Num a => a -> a -> a) -> Value -> Value -> EvalM Value
numOp _ op (VInt x) (VInt y) = return $ VInt $ x `op` y
numOp _ op (VDbl x) (VDbl y) = return $ VDbl $ x `op` y
numOp p _  v1       v2       = failOnValues p [v1, v2]

-- NB: evaluates deeply
equalValues :: Pos -> Value -> Value -> EvalM Bool
equalValues _ (VInt i1)    (VInt i2)    = return $ i1 == i2
equalValues _ (VDbl d1)    (VDbl d2)    = return $ d1 == d2
equalValues _ (VBool b1)   (VBool b2)   = return $ b1 == b2
equalValues _ (VChar c1)   (VChar c2)   = return $ c1 == c2
{- equalValues _ (VString s1) (VString s2) = return $ s1 == s2 -}
{- equalValues p v@VString{}  (VList xs)   = do -}
    {- v' <- toString p xs -}
    {- equalValues p v v' -}
{- equalValues p (VList xs)   v@VString{}  = do -}
    {- v' <- toString p xs -}
    {- equalValues p v' v -}
equalValues p (VList xs)   (VList ys)
    | length xs == length ys = and <$> zipWithM (equalValues p) xs ys
    | otherwise = return False
equalValues p (VMaybe m1)  (VMaybe m2)  =
    case (m1, m2) of
      (Just v1, Just v2) -> equalValues p v1 v2
      (Nothing, Nothing) -> return True
      _                  -> return False
equalValues p (VRecord m1) (VRecord m2) = do
    (ls1, vs1) <- unzip . recordValues <$> mapM force m1
    (ls2, vs2) <- unzip . recordValues <$> mapM force m2
    if length ls1 == length ls2 && length vs1 == length vs2
       then and <$> zipWithM (equalValues p) vs1 vs2
       else return False
equalValues p (VVariant l1 v1) (VVariant l2 v2)
    | l1 == l2  = join $ equalValues p <$> force v1 <*> force v2
    | otherwise = return False
equalValues p v1 v2 = failOnValues p [v1, v2]

-- NB: evaluates deeply
compareValues :: Pos -> Value -> Value -> EvalM Ordering
compareValues _ (VInt i1)    (VInt i2)    = return $ compare i1 i2
compareValues _ (VDbl d1)    (VDbl d2)    = return $ compare d1 d2
compareValues _ (VBool b1)   (VBool b2)   = return $ compare b1 b2
compareValues _ (VChar c1)   (VChar c2)   = return $ compare c1 c2
{- compareValues _ (VString s1) (VString s2) = return $ compare s1 s2 -}
{- compareValues p v@VString{}  (VList xs)   = do -}
    {- v' <- toString p xs -}
    {- compareValues p v v' -}
{- compareValues p (VList xs)   v@VString{}  = do -}
    {- v' <- toString p xs -}
    {- compareValues p v' v -}
compareValues p (VList xs)   (VList ys)   = go xs ys
  where
    go :: [Value] -> [Value] -> EvalM Ordering
    go []      []      = return EQ
    go (_:_)   []      = return GT
    go []      (_:_)   = return LT
    go (x:xs') (y:ys') = do
          c <- compareValues p x y
          if c == EQ
              then go xs' ys'
              else return c
compareValues p (VMaybe m1)  (VMaybe m2)  =
    case (m1, m2) of
      (Just v1, Just v2) -> compareValues p v1 v2
      (Nothing, Nothing) -> return EQ
      (Nothing, Just{} ) -> return LT
      (Just{} , Nothing) -> return GT
compareValues p v1 v2 = failOnValues p [v1, v2]

-- | Used for equality of records, sorts values by key
recordValues :: HashMap Label a -> [(Label, a)]
recordValues = List.sortBy (comparing fst) . HashMap.toList


-- | Optimise a list of chars
{- toString :: Pos -> [Value] -> EvalM Value -}
{- toString pos xs -}
    {- | Just cs <- mapM extractChar xs = return $ VString cs -}
    {- | otherwise = failOnValues pos xs -}

----------------

-- data TValue a where
  -- Value -> Type -> TValue a

-- TODO version of eval that returns a typed expression (using phantoms : monotypes only)
-- This should allow us to write a safe:
--
--   instance (ToValue a, FromValue b) => FromValue (a -> b) where
--      fromValueSafe :: MonadEval f => TypedValue (a -> b) -> f (a -> b)
--   toValueSafe :: ToValue a => a -> TypedValue a
--   refineValue :: ApplicativeError ... f => Value -> (forall a . TypedValue a -> f r) -> f r
--   unrefineValue :: TypedValue a -> Value

------------------------------------------------------------
-- FromValue class and instances

-- | How to marshall Haskell contructors and selectors into Expresso types.
-- TODO we just do something default for now
data Options = Options
defaultOptions :: Options
defaultOptions = Options

typeOf :: HasType a => Proxy a -> Type
typeOf = snd . typeOfWith defaultOptions NoCtx

-- | Haskell types with a corresponding Expresso type.
-- TODO generalize proxy?
class HasType a where

    typeOfWith :: Options -> Ctx -> Proxy a -> (Maybe String, Type)
    default typeOfWith :: (G.Generic a, GHasType (G.Rep a)) => Options -> Ctx -> Proxy a -> (Maybe String, Type)
    typeOfWith opts ct = gtypeOf opts ct . fmap G.from
class GHasType f where
    -- Give the Expresso type for a generic representation
    --
    -- Ctx is used to signify Record vs Variant context
    --
    -- The (Maybe String) contains constructor/selector names that we want to propagate to
    -- the outer level, so we can translate e.g. (Maybe a) as <Nothing, Just: a>
    gtypeOf :: Options -> Ctx -> Proxy (f x) -> (Maybe String, Type)

toValue :: ToValue a => a -> Value
toValue = toValueWith defaultOptions NoCtx

-- | Haskell types whose values can be converted to Expresso values.
class HasType a => ToValue a where
    toValueWith :: Options -> Ctx -> a -> Value
    default toValueWith :: (G.Generic a, GToValue (G.Rep a)) => Options -> Ctx -> a -> Value
    toValueWith opts ct = gtoValue opts ct . G.from
class GHasType f => GToValue f where
    gtoValue :: Options -> Ctx -> f x -> Value

-- | Haskell types whose values can be represented by Expresso values.
class HasType a => FromValue a where
    fromValue :: MonadEval f => Value -> f a
    default fromValue :: (G.Generic a, GFromValue (G.Rep a), MonadEval f) => Value -> f a
    fromValue x = G.to <$> gfromValue defaultOptions x
class GFromValue g where
    gfromValue :: MonadEval f => Options -> Value -> f (g x)

-- | This thing is passed around when traversing generic representations of Haskell types to keep track
-- of the surrounding context. We need this to properly decompose Haskell ADTs with >2 constructors into
-- proper (right-associative) rows. For records we also keep track of the number of elements, so we
-- can generate default selector functions _1, _2, _3 etc.
data Ctx = NoCtx | Var | Rec Int

setTag :: b -> (Maybe b, a) -> (Maybe b, a)
setTag b (_, a) = (Just b, a)


instance (GHasType f, G.Constructor c) => GHasType (G.M1 G.C c f) where
    gtypeOf opts ct = setTag (G.conName m) . gtypeOf opts ct . fmap G.unM1
      where m = (undefined :: t c f a)
instance (GHasType f, G.Selector c) => GHasType (G.S1 c f) where
    gtypeOf opts ct = setTag (G.selName m) . gtypeOf opts ct . fmap G.unM1
      where m = (undefined :: t c f a)
instance GHasType f => GHasType (G.D1 c f) where
    gtypeOf opts ct = gtypeOf opts ct . fmap G.unM1

instance GHasType (G.U1) where
    gtypeOf opts Rec{} _  = pure $ _TRowEmpty
    gtypeOf opts _ _    = pure $ _TRecord $ _TRowEmpty
instance GHasType (G.V1) where
    gtypeOf opts Var _ = pure $ _TRowEmpty
    gtypeOf opts _ _   = pure $ _TVariant $ _TRowEmpty

-- FIXME this allows infinite types to be generated, but is also necessary for valid cases
-- Can we forbid recursive Haskell types altogether?
instance HasType c => GHasType (G.K1 t c) where
    gtypeOf opts ct proxy = typeOfWith opts NoCtx (G.unK1 <$> proxy)

instance (GHasType f, GHasType g) => GHasType (f G.:+: g) where
  gtypeOf opts ct proxy =
    case gtypeOf opts NoCtx (leftP proxy) of
      -- Nothing is impossible, as we know the left branch will be a constructor (so the C1 instance is used)
      (Nothing, lType) -> error "GHasType (f G.:+: g): should not happen"
      (Just lLabel, lType) ->
        case gtypeOf opts Var (rightP proxy) of
          (Just rLabel, rType) -> pure $ tag ct (_TRowExtend lLabel lType (_TRowExtend rLabel rType _TRowEmpty))
          (Nothing, rType) ->     pure $ tag ct (_TRowExtend lLabel lType rType)
    where
      -- Emit variant tag whenever we're entering a variant context
      -- If we're already inside a variant, just emit the row type component
      tag Var = id
      tag ct  = _TVariant

instance (GHasType f, GHasType g) => GHasType (f G.:*: g) where
  gtypeOf opts ct proxy =
    case gtypeOf opts NoCtx (leftP proxy) of
      -- Nothing is impossible, as we know the left branch will be a selector (so the S1 instance is used)
      (Nothing, lType) -> error "GHasType (f G.:*: g): should not happen"
      (Just lLabel, lType) ->
        case gtypeOf opts (Rec $ succ $ used) (rightP proxy) of
          (Just rLabel, rType) -> pure $ tag ct (_TRowExtend (fl lLabel) lType (_TRowExtend (fr rLabel) rType _TRowEmpty))
          (Nothing, rType) ->     pure $ tag ct (_TRowExtend (fl lLabel) lType rType)
    where
      -- Replace empty field names with dummy names, so e.g. (4,5) becomes {_1:4,_2:5}
      fl "" = "_" ++ show (used + 1)
      fl x  = x
      fr "" = "_" ++ show (used + 2)
      fr x  = x

      used = case ct of
        (Rec n) -> n
        _ -> 0

      -- Emit record tag whenever we're entering a record context
      -- If we're already inside a record, just emit the row type component
      tag Rec{} = id
      tag ct    = _TRecord

leftP :: forall (q :: (k -> k) -> (k -> k) -> k -> k) f g a . Proxy ((f `q` g) a) -> Proxy (f a)
leftP _ = Proxy

rightP :: forall (q :: (k -> k) -> (k -> k) -> k -> k) f g a . Proxy ((f `q` g) a) -> Proxy (g a)
rightP _ = Proxy



instance GToValue f => GToValue (G.D1 c f) where
  gtoValue opts ct (G.M1 x) = gtoValue opts ct x

instance (GToValue f, G.Constructor c) => GToValue (G.C1 c f) where
  gtoValue opts ct (G.M1 x) = gtoValue opts ct x

instance (GToValue f, G.Selector c) => GToValue (G.S1 c f) where
  gtoValue opts ct (G.M1 x) = gtoValue opts ct x

instance GToValue G.U1 where
  gtoValue opts ct _ = VRecord mempty

instance GToValue G.V1 where
  gtoValue = error "absurd"

instance ToValue c => GToValue (G.K1 t c) where
  gtoValue opts ct v = toValueWith opts NoCtx (G.unK1 v)

instance (GToValue f, GToValue g) => GToValue (f G.:+: g) where
  gtoValue = error "TODO"

-- TODO get tag from underlying value...
instance (GToValue f, GToValue g) => GToValue (f G.:*: g) where
  gtoValue opts ct (l G.:*: r) =
    case valueToThunk $ gtoValue opts NoCtx l of
      lv -> case gtoValue opts (Rec $ succ $ used) r of
        -- TODO get labels..
        -- FIXME this record case depends on context...
        VRecord rv -> VRecord (HashMap.singleton "fox" lv <> rv)
        v          -> VRecord (HashMap.fromList [("foo", lv), ("bar", valueToThunk v)])
        {- v -> error $ "Expected VRecord, got " ++ show (ppValue v) -}
    where
      used = case ct of
        (Rec n) -> n
        _ -> 0


-- TODO for testing...
data P a b = P { a :: a, b :: b } deriving (G.Generic)
instance (HasType a, HasType b) => HasType (P a b)
instance (ToValue a, ToValue b) => ToValue (P a b)
data T a b c = T { x :: a, y :: b, z :: c } deriving (G.Generic)
instance (HasType a, HasType b, HasType c) => HasType (T a b c)
instance (ToValue a, ToValue b, ToValue c) => ToValue (T a b c)


instance GFromValue f => GFromValue (G.D1 c f) where
  gfromValue = error "TODO"
instance GFromValue f => GFromValue (G.C1 c f) where
  gfromValue = error "TODO"
instance GFromValue f => GFromValue (G.S1 c f) where
  gfromValue = error "TODO"
instance GFromValue (G.K1 t c) where
  gfromValue opts = error "absurd"
instance GFromValue G.U1 where
  gfromValue opts _ = pure G.U1
instance GFromValue G.V1 where
  gfromValue = error "TODO"
instance (GFromValue f, GFromValue g) => GFromValue (f G.:+: g) where
  gfromValue = error "TODO"
instance (GFromValue f, GFromValue g) => GFromValue (f G.:*: g) where
  gfromValue = error "TODO"



instance HasType Integer where
    typeOfWith _ _ _ = pure $ _TInt
instance HasType Int where
    typeOfWith _ _ _ = pure $ _TInt
instance HasType Double where
    typeOfWith _ _ _ = pure $ _TDbl
instance HasType Char where
    typeOfWith _ _ _ = pure $ _TChar
instance HasType a => HasType [a] where
    typeOfWith opts ct p = _TList <$> typeOfWith opts ct (inside p)
instance (HasType a, HasType b) => HasType (a -> b) where
    typeOfWith opts ct p = _TFun <$> (typeOfWith opts ct $ dom p) <*> (typeOfWith opts ct $ inside p)

instance HasType Void
instance HasType ()
instance HasType Bool
instance HasType Ordering
-- FIXME remove Maybe/Char from lang, add Text
instance (HasType a) => HasType (Maybe a)
instance (HasType a, HasType b) => HasType (Either a b)
instance (HasType a, HasType b) => HasType (a, b)
instance (HasType a, HasType b, HasType c) => HasType (a, b, c)
instance (HasType a, HasType b, HasType c, HasType d) => HasType (a, b, c, d)
-- TODO Vector/Set (as []), map as [Entry]


{- FIXME move -}
{- <Leaf:Int | <Node:{left:Int,right:[Int]} | <>>> -}
{- data Foo a = Leaf a | Node { left :: a, right :: a } -}
  {- deriving G.Generic -}
{- instance (HasType a) => HasType (Foo a) -}
{- instance ToValue a => ToValue (Foo a) -}
{- instance FromValue a => FromValue (Foo a) -}

{- data Tree a = TLeaf a | TNode { tleft :: a, tright :: Tree a } -}
  {- deriving G.Generic -}
{- instance (HasType a) => HasType (Tree a) -}
{- instance ToValue a => ToValue (Foo a) -}

inside :: proxy (f a) -> Proxy a
inside = const Proxy

dom :: proxy (a -> b) -> Proxy a
dom = const Proxy

codom :: proxy (a -> b) -> Proxy b
codom = inside


instance ToValue ()
instance ToValue Void
instance ToValue Integer where
    toValueWith _ _ = VInt
instance ToValue Int where
    toValueWith _ _ = VInt . fromIntegral
instance ToValue Double where
    toValueWith _ _ = VDbl
instance ToValue Char where
    toValueWith _ _ = VChar
instance ToValue a => ToValue [a] where
    toValueWith _ _ = VList . fmap toValue

instance FromValue Integer where
    fromValue (VInt i) = return i
    fromValue v        = failfromValue "VInt" v

instance FromValue Int where
    fromValue x = fromInteger <$> fromValue x

instance FromValue Double where
    fromValue (VDbl d) = return d
    fromValue v        = failfromValue "VDbl" v

-- TODO derive
instance FromValue Bool
{- instance FromValue Bool where -}
    {- fromValue (VBool b) = return b -}
    {- fromValue v         = failfromValue "VBool" v -}

instance FromValue Char where
    fromValue (VChar c) = return c
    fromValue v         = failfromValue "VChar" v

instance FromValue a => FromValue (Maybe a)
{- instance FromValue a => FromValue (Maybe a) where -}
    {- fromValue (VMaybe m) = mapM fromValue m -}
    {- fromValue v          = failfromValue "VMaybe" v -}

instance
--  {-# OVERLAPS #-}
  FromValue String where
    {- fromValue (VString s) = return s -}
    fromValue (VList xs)  = traverse getC xs
    fromValue v           = failfromValue "VString" v
      where
{- getC :: Value -> EvalM Char -}
getC (VChar c) = pure c
getC v = failfromValue "VString" v

instance FromValue a => FromValue [a] where
    fromValue (VList xs) = mapM fromValue xs
    fromValue v          = failfromValue "VList" v

fromValueL fromValue (VList xs) = mapM fromValue xs
fromValueL _         v          = failfromValue "VList" v

-- FIXME carry type in class to make this safe
instance (ToValue a, FromValue b) => FromValue (a -> b) where
    fromValue (VLam f) = fmap (fmap $ either (error "unexpected") id) $ pure $ \x -> runEvalM' $ do
      x <- (mkThunk $ pure $ toValue x)
      r <- f x
      fromValue r
    fromValue v           = failfromValue "VLam" v


-- FIXME remove
-- | A record where all fields have the same type.
instance HasType a => HasType (HashMap Name a) where
    typeOfWith = error "Impossible: FIXME rewrite tests to use real HS records instead of faking it"
instance FromValue a => FromValue (HashMap Name a) where
    fromValue (VRecord m) = mapM fromValue' m
    fromValue v           = failfromValue "VRecord" v


fromValueRTh (VRecord m) = return m
fromValueRTh v           = failfromValue "VRecord" v

failfromValue :: MonadError String f => String -> Value -> f a
failfromValue desc v = throwError $ "Expected a " ++ desc ++
    ", but got: " ++ show (ppValue v)


