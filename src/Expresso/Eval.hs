{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# OPTIONS_GHC -fno-warn-unused-binds #-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE PatternSynonyms #-}
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

#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

------------------------------------------------------------
--
-- A lazy evaluator.
--
-- The front-end syntax is simple, so we evaluate it directly.
--
module Expresso.Eval(
    eval
  , runEvalM'
  , runEvalIO
  , Env
  , EvalM
  , Value(..)
  , ppValue
  , ppValue'
  , force
  , mkThunk
  , bind

  , HasType(..)
  , FromValue(..)
  , ToValue(..)


  -- TODO testing
  , V1(..)
  , V2(..)
  , V3(..)
  , V4(..)
  , roundTrip
)
where

import Data.Hashable
import Control.Monad.Except hiding (mapM)
import Control.Monad.State hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Applicative
import Data.Bifunctor (first)
import Data.Functor.Compose
import Data.Foldable (foldrM, toList)
import Data.Map (Map)
import Data.HashMap.Strict (HashMap)
import Data.Coerce
import Data.Maybe
import Data.Monoid
import Data.Ord
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HashMap
import qualified Data.List as List
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as T
import Control.Monad.ST
import Data.STRef
import Data.Void
import Data.Functor.Identity
import Data.Proxy
import qualified GHC.Generics as G
import GHC.TypeLits
import Control.Exception (IOException, catch)

import Expresso.Syntax
import Expresso.Type
import Expresso.Pretty
import Expresso.Utils (cata, (:*:)(..), K(..))
import qualified Expresso.Parser as Parser

#if __GLASGOW_HASKELL__ <= 708
import Prelude hiding (mapM, concat, elem, and, any)
import Data.Foldable
import Data.Traversable
#endif


{- import Debug.Trace -}

-- |
-- Call-by-need environment
-- A HashMap makes it easy to support record wildcards
type Env = HashMap Name Thunk

newtype EvalM a = EvalM { runEvalT :: ExceptT String Identity a }
deriving instance Functor EvalM
deriving instance Applicative EvalM
deriving instance Monad EvalM
deriving instance MonadError String EvalM

newtype Thunk = Thunk { force_ :: EvalM Value }

type ApplicativeMonadError e f = (Applicative f, Alternative f, MonadError e f)

class ApplicativeMonadError String f => MonadEval f where
  force :: Thunk -> f Value
instance Alternative EvalM where
  EvalM a <|> EvalM b = EvalM (a <|> b)
  empty = EvalM empty
instance MonadEval EvalM where
  force = force_


{- data EvalIO a = EvalIO { runEvalIO :: IO a } -}
  {- deriving (Functor, Applicative, Monad) -}
{- instance MonadError EvalIO where -}
  {- throwError = error -}
  {- catchError = error "TODO" -}

{- -- Note: Throwaway IO instance with bad 'catch' behavior -}
{- -- Do not use for serious code... -}
{- instance MonadEval EvalIO where -}
  {- force = runEvalIO . force -}
    {- where -}
runEvalIO :: EvalM a -> IO a
runEvalIO = either error pure . runEvalM'


instance Show Thunk where
    show _ = "<Thunk>"

mkThunk :: EvalM Value -> EvalM Thunk
mkThunk = return . Thunk

data Value
  = VLam     !(Thunk -> EvalM Value)
  | VInt     !Integer
  | VDbl     !Double
  | VBool    !Bool
  | VChar    !Char
  {- | VMaybe   !(Maybe Value) -}
  | VList    ![Value] -- lists are strict
  | VRecord  !(HashMap Label Thunk) -- field order no defined
  | VVariant !Label !Thunk

instance Show Value where
  show = showR . runEvalM' . ppValue'

valueToThunk :: Value -> Thunk
valueToThunk = Thunk . pure

-- | This does *not* evaluate deeply
ppValue :: Value -> Doc
ppValue (VLam  _)   = "<Lambda>"
ppValue (VInt  i)   = integer i
ppValue (VDbl  d)   = double d
ppValue (VBool b)   = if b then "True" else "False"
ppValue (VChar c)   = text $ c : []
{- ppValue (VMaybe mx) = maybe "Nothing" (\v -> "Just" <+> ppParensValue v) mx -}
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
        {- VMaybe{}   -> parens $ ppValue v -}
        VVariant{} -> parens $ ppValue v
        _          -> ppValue v

-- | This evaluates deeply
ppValue' :: Value -> EvalM Doc
ppValue' (VRecord m) = (bracesList . map ppEntry . List.sortBy (comparing fst) . HashMap.toList)
                           <$> mapM (force >=> ppValue') m
  where
    ppEntry (l, v) = text l <+> text "=" <+> v
ppValue' (VVariant l t) = (text l <+>) <$> (force >=> ppParensValue') t
ppValue' v = return $ ppValue v

ppParensValue' :: Value -> EvalM Doc
ppParensValue' v =
    case v of
        {- VMaybe{}   -> parens <$> ppValue' v -}
        VVariant{} -> parens <$> ppValue' v
        _          -> ppValue' v

extractChar :: Value -> Maybe Char
extractChar (VChar c) = Just c
extractChar _ = Nothing


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
    String s      -> VList (fmap VChar s)
    Show          -> mkStrictLam $ \v -> string . show <$> ppValue' v
      where
        string = VList . fmap VChar
    ErrorPrim     -> VLam $ \s -> do
        msg <- fromValue' s
        throwError $ "error (" ++ show pos ++ "):" ++ msg

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

    {- JustPrim      -> mkStrictLam $ \v -> return $ VMaybe (Just v) -}
    {- NothingPrim   -> VMaybe Nothing -}
    {- MaybePrim     -> VLam $ \x -> return $ mkStrictLam2 $ \f v -> -}
        {- case v of -}
            {- VMaybe (Just v') -> evalApp pos f (Thunk $ return v') -}
            {- VMaybe Nothing   -> force x -}
            {- _                -> failOnValues pos [v] -}

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
equalValues p (VList xs)   (VList ys)
    | length xs == length ys = and <$> zipWithM (equalValues p) xs ys
    | otherwise = return False
{- equalValues p (VMaybe m1)  (VMaybe m2)  = -}
    {- case (m1, m2) of -}
      {- (Just v1, Just v2) -> equalValues p v1 v2 -}
      {- (Nothing, Nothing) -> return True -}
      {- _                  -> return False -}
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
{- compareValues p (VMaybe m1)  (VMaybe m2)  = -}
    {- case (m1, m2) of -}
      {- (Just v1, Just v2) -> compareValues p v1 v2 -}
      {- (Nothing, Nothing) -> return EQ -}
      {- (Nothing, Just{} ) -> return LT -}
      {- (Just{} , Nothing) -> return GT -}
compareValues p v1 v2 = failOnValues p [v1, v2]

-- | Used for equality of records, sorts values by key
recordValues :: HashMap Label a -> [(Label, a)]
recordValues = List.sortBy (comparing fst) . HashMap.toList




-- |
-- How to marshall Haskell contructors and selectors into Expresso types.
--
-- Included to make it easier to add options later...
data Options = Options

defaultOptions :: Options
defaultOptions = Options


-- | Haskell types with a corresponding Expresso type.
-- TODO generalize proxy?
class HasType a where
    typeOf :: HasType a => Proxy a -> Type
    default typeOf :: (G.Generic a, GHasType (G.Rep a)) => Proxy a -> Type
    typeOf = either id (renderADT . improveADT) . gtypeOf defaultOptions . fmap G.from

-- | Haskell types whose values can be converted to Expresso values.
--
-- We expect
--
-- @
-- typeOf (pure a) = typeOfValue (toValue a)
-- @
--
-- If a type is an instance of both 'FromValue' and 'ToValue', we expect:
-- @
-- fromValue . toValue = pure
-- @
class HasType a => ToValue a where
    toValue :: ToValue a => a -> Value
    default toValue :: (G.Generic a, GToValue (G.Rep a)) => a -> Value
    toValue = renderADTValue . improveADT . gtoValue defaultOptions . G.from

-- | Haskell types whose values can be represented by Expresso values.
class HasType a => FromValue a where
    fromValue :: MonadEval f => Value -> f a
    default fromValue :: (G.Generic a, ADFor (G.Rep a) ~ Var, GFromValue (G.Rep a), MonadEval f) => Value -> f a
    fromValue = runParser . fmap G.to . renderADParser . fixADNames $ gfromValue defaultOptions Proxy
    {- fromValue = error "fromValue" -}

class GHasType f where
    gtypeOf :: Options -> Proxy (f x) -> Either Type (ADT Type)
class GHasType f => GToValue f where
    gtoValue :: Options -> f x -> ADT Value
class GHasType f => GFromValue f where
    type ADFor f :: C
    gfromValue :: MonadEval g => Options -> Proxy (f x) -> AD (ADFor f) (Parser g) (f x)

-- | This thing is passed around when traversing generic representations of Haskell types to keep track
-- of the surrounding context. We need this to properly decompose Haskell ADTs with >2 constructors into
-- proper (right-associative) rows. For records we also keep track of the number of elements, so we
-- can generate default selector functions _1, _2, _3 etc.
{- data Ctx = NoCtx | Var | Rec Int -}
  {- deriving (Show) -}

{- setTag :: b -> (Maybe b, a) -> (Maybe b, a) -}
{- setTag b (_, a) = (Just b, a) -}

-- TODO this is not super-typed...

type ConstructorName = Name
type SelectorName = Name

-- | An algebraic data type.
data ADT a = ADT { getADT :: Map ConstructorName (Map SelectorName a) }
  deriving (Eq, Show, Functor)

-- | Replace all auto-generated names in products.
-- E.g. rewrites
--
--  {___a:A, ___b:B} -> {_1:A, _2:B}
fixConsNames :: ADT a -> ADT a
fixConsNames (ADT outer) = ADT (g <$> outer)
  where
    g inner
      | hasAutoKeys inner = replaceKeys (fmap (("_" <>) . show) [1..]) inner
      | otherwise = inner


    replaceKeys :: (Ord k, Hashable k) => [k] -> Map k a -> Map k a
    replaceKeys ks m = Map.fromList $ zip ks $ fmap snd $ Map.toList m

    -- TODO ugly hack, see below
    hasAutoKeys x = case List.find ("___" `List.isInfixOf`) $ Map.keys x of
      Nothing -> False
      _ -> True


improveADT :: ADT a -> ADT a
improveADT = fixConsNames

{-

  NOTE encoding variations:
    Note that the following types are isomorphic, but have different types and representations
    in Expresso:
      A
      {foo:A}
      <Foo:A>
    More notably, these unify:
      {bar:A,...} ~ {bar:A}
    while these do not:
      {bar:A,...} ~ A

    This gives us some ambiguity when encoding HS types.

    Removing singleton variants gives more natural encoding for normal tuples
      () ~ {}                 instead of  <() : {}>
      (a,b) ~ {_1:a, _2:b}    instead of  <(,) : {_1:a, _2:b}>
    but has the drawback of 'collapsing' newtypes:
      Sum Int ~ Int           insted of <Sum : Int>

    Disallowing singleton products is probably uncontroversial.
 -}


data C = Var | Rec | None
class NotVar c
instance NotVar None
instance NotVar Rec

-- Haskell style ADT
--
-- This could be relaxed to normal row-polymorphism by relaxing the constraint on selectors
data AD :: C -> (* -> *) -> * -> * where
  Singleton :: f a -> AD None f a
  -- Constructor/Selector 'resets' the prod/coprod context
  Constructor :: NotVar x   => String -> AD x f a -> AD Var f a
  Selector    :: (x ~ None) => String -> AD x f a -> AD Rec f a -- A Prod can only contain other Prods, Selector, or Terminal
  -- This implies every field has to be named
  Prod :: (a -> b -> c) -> AD Rec f a -> AD Rec f b -> AD Rec f c
  Terminal :: f a -> AD Rec f a

  -- A coprod can only contain other Coprods, Constructor, or Initial
  -- This implies every alternative has to be named
  Coprod :: (a -> c) -> (b -> c) -> AD Var f a -> AD Var f b -> AD Var f c
  Initial :: AD Var f a

data AD' where
  Singleton' :: AD'
  Constructor' :: String -> AD' -> AD'
  Selector' :: String -> AD' -> AD'
  Prod' :: AD' -> AD' -> AD'
  Coprod' :: AD' -> AD' -> AD'
  Initial' :: AD'
  Terminal' :: AD'
  deriving (Show)

instance Show (AD x f a) where
  show = show . go
    where
      go :: forall x f a . AD x f a -> AD'
      go (Singleton _) = Singleton'
      go (Constructor n a) = Constructor' n $ go a
      go (Selector n a) = Selector' n $ go a
      go (Prod _ a b) = Prod' (go a) (go b)
      go (Coprod _ _ a b) = Coprod' (go a) (go b)
      go Initial = Initial'
      go Terminal{} = Terminal'

instance Functor f => Functor (AD x f) where
  fmap f (Singleton fa) = Singleton $ fmap f fa
  fmap f (Constructor n x) = Constructor n (fmap f x)
  fmap f (Selector n x) = Selector n (fmap f x)
  fmap f (Terminal fa) = Terminal $ fmap f fa
  fmap f Initial = Initial
  fmap f (Prod g a b) = Prod (\a b -> f $ g a b) a b
  fmap f (Coprod g h a b) = Coprod (f . g) (f . h) a b


renderADT :: ADT Type -> Type
renderADT (ADT outer)
  = foldOrSingle
    _TVariant (\k v -> _TRowExtend k (g v)) _TRowEmpty
    -- Remove singleton variants
    (\k m -> g m)
    -- Allowing them would look like this (e.g. a normal foldrWithKey)
    {- (\k v -> _TVariant $ _TRowExtend k (g v) _TRowEmpty) -}
    outer
  where
    g inner
      = foldOrSingle
        _TRecord (\k v -> _TRowExtend k v) _TRowEmpty
          -- A fold for general products/records
        (flip const)
        -- Remove singleton products
        {- (\k v -> _TRecord $ _TRowExtend k v _TRowEmpty) -}
        inner


renderADTValue :: ADT Value -> Value
renderADTValue (ADT outer)
  = foldOrSingle
    -- TODO clean up this error printing...
    id (\k v r -> error $ "unexpected variant with >1 element" <> show (k,runEvalM'.ppValue' $ g v,runEvalM'.ppValue' $ r)) (error "absurd!")
    (\k v -> VVariant k $ valueToThunk $ g v)
    outer
  where
    g inner
      = foldOrSingle
        VRecord (\k v -> HashMap.insert k (valueToThunk v)) mempty
        (\_ v -> v)
        inner

-- Would be a nice implementation, but the (Alternative Compose ...) instance is too restrictive
--
-- DerivingVia anyone?
--
--     type Parser f = ((->) Value) `Compose` f
--     _Parser = Compose
--     runParser = getCompose

-- FIXME when composed with EvalM, this concatenates error messages...
type Parser f = ReaderT Value f
_Parser = ReaderT
runParser = runReaderT



intoRecord :: (Applicative f, MonadState RecNames f) => f ()
intoRecord = put $ RecNames 1

nextName :: (Applicative f, MonadState RecNames f) => f (Maybe String)
nextName = do
  st <- get
  case st of
    RecNamesInit -> pure Nothing
    RecNames n -> do
      put $ RecNames $ n + 1
      pure $ Just $ "_" <> show n

chooseP :: Alternative f => Parser f a -> Parser f a -> Parser f a
chooseP = (<|>)

-- FIXME
{- traceP x = trace (show x) x -}


data RecNames
  = RecNamesInit -- We are not in a product
  | RecNames Int -- We are in a product, and this is the next name to generate

-- | Remove singleton selectors.
-- Rename anonymous '' selectors with _1, _2 etc.
fixADNames :: AD Var f a -> AD Var f a
fixADNames x = evalState (go x) RecNamesInit
  where
    go :: AD Var f a -> State RecNames (AD Var f a)
    go x@Initial{} = pure x
    go (Coprod f g x y) = Coprod f g <$> go' x <*> go' y
    go (Constructor k a) = Constructor k <$> go' a

    go' :: AD x f a -> State RecNames (AD x f a)
    go' x@Singleton{} = pure x
    go' x@Terminal{} = pure x
    go' (Prod f x y) = do
      intoRecord
      Prod f <$> go' x <*> go' y
    go' (Selector k a) = do
      name <- nextName
      case name of
        Nothing -> Selector "" <$> go' a
        Just n  -> Selector n <$> go' a
    go' x@Initial{} = go x
    go' x@Coprod{} = go x
    go' x@Constructor{} = go x

renderADParser :: MonadEval f => AD Var (Parser f) a -> Parser f a
renderADParser x = evalState (go x) 0
  where
    go :: forall f a . MonadEval f => AD Var (Parser f) a -> State Int (Parser f a)
    go Initial = pure empty
    go (Coprod f g x y) = liftA2 (chooseP) (fmap f <$> go x) (fmap g <$> go y)
    go (Constructor k a) = do
      p <- go' a
      pure $ _Parser $ \x -> case x of
        (VVariant n th) | n == k -> do
          y <- force th
          runParser p y
        _ -> throwError $ "Bad variant, wanted " <> k <> " got (" <> show (ppValue x) <> ")"

    go' :: forall f x a . MonadEval f => AD x (Parser f) a -> State Int (Parser f a)
    go' (Singleton p) = pure p
    go' (Terminal x) = pure x
    go' (Prod f x y) = do
      a' <- go' x
      b' <- go' y
      pure $ liftA2 f a' b'
    go' (Selector k x) = do
      p <- go' x
      case k of
        "" -> pure p
        _ ->
          pure $ _Parser $ \x -> case x of
            (VRecord m) -> case HashMap.lookup k m of
              Just th -> do
                v <- force th
                runParser p v
              _ -> fail k m
            _ -> throwError $ "Not a record, wanted '"<> k <>"', got (" <> (showR $ runEvalM' $ ppValue' x) <> ")"
      where
        fail k m = throwError $ "Bad record, wanted '" <> k <> "', got rec with keys " <> show (HashMap.keys m)

    go' x@Initial{} = go x
    go' x@Coprod{} = go x
    go' x@Constructor{} = go x

liftP2 :: (a -> b -> c) -> f a -> f b -> f c
{- liftP2 = liftA2 -}
liftP2 = undefined

-- TODO move
foldOrSingle :: (b -> c) -> (k -> a -> b -> b) -> b -> (k -> a -> c) -> Map k a -> c
foldOrSingle post f z o x = case Map.toList x of
  [(k, v)] -> o k v
  _ -> post $ Map.foldrWithKey f z x

singleton :: a -> ADT a
singleton v = ADT $ Map.singleton "" $ Map.singleton "" v

selector :: SelectorName -> ADT a -> ADT a
selector k (ADT outer) = ADT (g <$> outer)
  where
    g inner
      | Map.size inner == 1 = Map.singleton k (head $ toList inner)
      | otherwise = error "ADT: Unexpected"

constructor :: SelectorName -> ADT a -> ADT a
constructor k (ADT outer) = ADT $ g outer
  where
    g x
      | Map.size x == 1 = Map.singleton k (head $ toList x)
      | otherwise = error "ADT: Unexpected"


prod :: ADT a -> ADT a -> ADT a
prod (ADT l) (ADT r)
  | hasAmbNamesF l || hasAmbNamesF r = ADT $ Map.unionWith unionDisamb l r
  | otherwise                        = ADT $ Map.unionWith Map.union l r
  where
    hasAmbNamesF = any hasAmbNames
    hasAmbNames :: Map Name a -> Bool
    hasAmbNames = not . null . filter (== "") . Map.keys

    -- Haskell allows positional products (aka "tuples"), so we need to
    -- make up names to avoid ambiguity.
    --
    -- As we don't know how products will be nested, we just make up something
    -- preserving order. At the top level we will overwrite this with: _1, _2,
    -- etc.
    --
    -- TODO this is a hack, replace the special strings with (Either [Int] String)
    -- or something.
    unionDisamb :: Map Name a -> Map Name a -> Map Name a
    unionDisamb a b = mapKeys ("___a"<>) a `Map.union` mapKeys ("___b"<>) b

    mapKeys f = Map.fromList . fmap (first f) . Map.toList

coprod :: ADT a -> ADT a -> ADT a
coprod (ADT l) (ADT r) = ADT (l `Map.union` r)

inL :: ADT a -> ADT a
inR :: ADT a -> ADT a
inL = id
inR = id


initial :: ADT a
initial = ADT mempty

terminal :: ADT a
terminal = ADT (Map.singleton "()" $ mempty)

-- FIXME test
at1 =  ppType $ renderADT $ improveADT $
  (constructor "Foo"
    (selector "a" (singleton _TInt) `prod` selector "b" (singleton (_TList _TInt))))
  `coprod`
  (constructor "B" $ singleton _TInt)
-- FIXME test
at2 = runEvalM' $ ppValue' $ renderADTValue $ improveADT $
  (constructor "Foo"
    (selector "a" (singleton $ VInt 2) `prod` selector "b" (singleton (VList [VInt 33]))))
  {- (constructor "B" $ singleton $ VRecord mempty) -}


{- pattern SimpleType a = Left a -}
{- pattern AlgType a    = Right a -}

pattern Id a = G.M1 a
runId = G.unM1
runConst = G.unK1

-- TODO remove Either in return type of gtypeOf if Left is not used...
-- TODO move
instance (GHasType f, G.Constructor c) => GHasType (G.C1 c f) where
  gtypeOf opts x = fmap (constructor $ G.conName m) $ gtypeOf opts (runId <$> x)
    where m = (undefined :: t c f a)
instance (GHasType f, G.Selector c) => GHasType (G.S1 c f) where
  gtypeOf opts x = fmap (selector $ G.selName m) $ gtypeOf opts (runId <$> x)
    where m = (undefined :: t c f a)
instance GHasType f => GHasType (G.D1 c f) where
  gtypeOf opts x = gtypeOf opts (runId <$> x)

instance GHasType (G.U1) where
  gtypeOf _ _ = pure $ terminal
instance GHasType (G.V1) where
  gtypeOf _ _ = pure $ initial
instance HasType c => GHasType (G.K1 t c) where
  -- FIXME recurse with opts
  -- hows does aeson achieve it (without polluting the top-level class?)
  gtypeOf opts p = pure $ singleton $ typeOf (runConst <$> p)
instance (GHasType f, GHasType g) => GHasType (f G.:+: g) where
  gtypeOf opts p = coprod <$> (gtypeOf opts lp) <*> (gtypeOf opts rp)
    where
      lp = leftP p
      rp = rightP p
instance (GHasType f, GHasType g) => GHasType (f G.:*: g) where
  gtypeOf opts p = prod <$> (gtypeOf opts lp) <*> (gtypeOf opts rp)
    where
      lp = leftP p
      rp = rightP p



leftP :: forall (q :: (k -> k) -> (k -> k) -> k -> k) f g a . Proxy ((f `q` g) a) -> Proxy (f a)
leftP _ = Proxy

rightP :: forall (q :: (k -> k) -> (k -> k) -> k -> k) f g a . Proxy ((f `q` g) a) -> Proxy (g a)
rightP _ = Proxy



instance (GToValue f, G.Constructor c) => GToValue (G.C1 c f) where
  gtoValue opts x = (constructor $ G.conName m) $ gtoValue opts (runId x)
    where m = (undefined :: t c f a)

instance (GToValue f, G.Selector c) => GToValue (G.S1 c f) where
  gtoValue opts x = (selector $ G.selName m) $ gtoValue opts (runId x)
    where m = (undefined :: t c f a)

instance GToValue f => GToValue (G.D1 c f) where
  gtoValue opts x = gtoValue opts (runId x)

instance ToValue c => GToValue (G.K1 t c) where
  gtoValue opts p = singleton $ toValue (runConst $ p)

instance GToValue G.U1 where
  gtoValue _ _ = terminal

instance GToValue G.V1 where
  gtoValue _ _ = initial

instance (GToValue f, GToValue g) => GToValue (f G.:+: g) where
  gtoValue opts (G.L1 x) = inL (gtoValue opts x)
  gtoValue opts (G.R1 x) = inR (gtoValue opts x)

-- TODO get tag from underlying value...
instance (GToValue f, GToValue g) => GToValue (f G.:*: g) where
  gtoValue opts (lp G.:*: rp) = prod (gtoValue opts lp) (gtoValue opts rp)


_Id :: f x -> G.M1 t c f x
_Id = G.M1

_Const :: c -> G.K1 i c x
_Const = G.K1


instance (GFromValue f, NotVar (ADFor f), G.Constructor c) => GFromValue (G.C1 c f) where
  type ADFor (G.C1 c f) = Var
  gfromValue opts p = fmap _Id $ Constructor (G.conName m) $ gfromValue opts (runId <$> p)
    where m = (undefined :: t c f a)
instance (GFromValue f, ADFor f ~ None, G.Selector c) => GFromValue (G.S1 c f) where
  type ADFor (G.S1 c f) = Rec
  gfromValue opts p = fmap _Id $ Selector (G.selName m) $ gfromValue opts (runId <$> p)
    where m = (undefined :: t c f a)
instance GFromValue f => GFromValue (G.D1 c f) where
  type ADFor (G.D1 c f) = ADFor f
  gfromValue opts p = fmap _Id $ gfromValue opts (runId <$> p)
instance FromValue c => GFromValue (G.K1 t c) where
  type ADFor (G.K1 t c) = None
  gfromValue opts p = Singleton $ fmap _Const $ _Parser fromValue
instance GFromValue G.U1 where
  type ADFor G.U1 = Rec
  gfromValue opts p = Terminal (pure $ G.U1)
instance GFromValue G.V1 where
  type ADFor G.V1 = Var
  gfromValue opts p = Initial
instance (GFromValue f, GFromValue g, ADFor f ~ Var, ADFor g ~ Var) => GFromValue (f G.:+: g) where
  type ADFor (f G.:+: g) = Var
  gfromValue opts p = Coprod (G.L1) (G.R1) (gfromValue opts lp) (gfromValue opts rp)
    where
      lp = leftP p
      rp = rightP p
instance (GFromValue f, GFromValue g, ADFor f ~ Rec, ADFor g ~ Rec) => GFromValue (f G.:*: g) where
  type ADFor (f G.:*: g) = Rec
  gfromValue opts p = Prod (G.:*:) (gfromValue opts lp) (gfromValue opts rp)
    where
      lp = leftP p
      rp = rightP p






inside :: proxy (f a) -> Proxy a
inside = const Proxy

dom :: proxy (a -> b) -> Proxy a
dom = const Proxy

codom :: proxy (a -> b) -> Proxy b
codom = inside


instance HasType Integer where
    typeOf _ = _TInt

instance ToValue Integer where
    toValue = VInt

instance FromValue Integer where
    fromValue (VInt i) = return i
    fromValue v        = failfromValue "VInt" v

instance HasType Int where
    typeOf _ = _TInt

instance ToValue Int where
    toValue = VInt . fromIntegral

instance FromValue Int where
    fromValue x = fromInteger <$> fromValue x

instance HasType Double where
    typeOf _ = _TDbl

instance ToValue Double where
    toValue = VDbl

instance FromValue Double where
    fromValue (VDbl d) = return d
    fromValue v        = failfromValue "VDbl" v

instance HasType Bool where
  typeOf _ = _TBool
instance ToValue Bool where
    toValue = VBool
instance FromValue Bool where
    fromValue (VBool b) = return b
    fromValue v         = failfromValue "VBool" v

instance ToValue Char where
    toValue = VChar
instance FromValue Char where
    fromValue (VChar c) = return c
    fromValue v         = failfromValue "VChar" v
instance HasType Char where
    typeOf _ = _TChar




instance (HasType a, HasType b) => HasType (a -> f b) where
    typeOf p = _TFun (typeOf $ dom p) (typeOf $ inside $ inside p)

instance (ToValue a, FromValue b, MonadEval f) => FromValue (a -> f b) where
    fromValue (VLam f) = pure  $ \x -> liftEval $ do
      x <- (mkThunk $ pure $ toValue x)
      r <- f x
      fromValue r
      where
        -- TODO for now we always run in the pure evaluation monad (which is
        -- hardcoded in the Value type).
        --
        -- This natural transformation lifts the evaluator into the user-providec
        -- evaluator. In theory we could parameterize (Exp, Value, Type) etc
        -- on some effect algebra and provide the interpreter function here.
        liftEval = either throwError pure . runEvalM'

    fromValue v           = failfromValue "VLam" v

fv2 :: (MonadEval m, FromValue b, ToValue a) =>
     Value -> a -> m b
fv2 = (\f a b -> (f a >>= ($ b))) fromValue

fv3 :: (MonadEval m, FromValue r, ToValue a, ToValue b) =>
     Value -> a -> b -> m r
fv3 = (\f a b c -> (f a >>= ($ b) >>= ($ c))) fromValue




instance HasType a => HasType [a] where
    typeOf p = _TList $ typeOf (inside p)

instance ToValue a => ToValue [a] where
  toValue = VList . fmap toValue
instance FromValue a => FromValue [a] where
    fromValue (VList xs) = mapM fromValue xs
    fromValue v          = failfromValue "VList" v

-- TODO make up my mind re: Maybe...
instance ToValue a => ToValue (Maybe a) where
instance (HasType a) => HasType (Maybe a)
instance FromValue a => FromValue (Maybe a) where



-- We can't derive Void as its recursively defined...
instance HasType Void where
  typeOf _ = _TVariant _TRowEmpty
instance ToValue Void
instance FromValue Void

instance HasType ()
instance FromValue () where
    fromValue _ = pure ()
instance ToValue () where
  toValue _ = VRecord mempty


instance HasType LBS.ByteString where
  typeOf _ = _TBlob
instance ToValue LBS.ByteString where
  toValue = error "TODO ByteString"
instance FromValue LBS.ByteString where
  fromValue = error "TODO ByteString"

instance HasType T.Text where
  typeOf _ = _TText
instance ToValue T.Text where
  toValue = error "TODO Text"
instance FromValue T.Text where
  fromValue = error "TODO Text"

instance
#if __GLASGOW_HASKELL__ > 708
  {-# OVERLAPS #-}
#endif
  FromValue String where
    {- fromValue (VString s) = return s -}
    fromValue (VList xs)  = traverse getC xs
    fromValue v           = failfromValue "VString" v
      where

getC :: MonadEval f => Value -> f Char
getC (VChar c) = pure c
getC v = failfromValue "VString" v












-- TODO

instance HasType Ordering

instance (HasType a, HasType b) => HasType (Either a b)
instance (HasType a, HasType b) => HasType (a, b)
instance (HasType a, HasType b, HasType c) => HasType (a, b, c)
instance (HasType a, HasType b, HasType c, HasType d) => HasType (a, b, c, d)
instance (ToValue a, ToValue b) => ToValue (Either a b)
instance (FromValue a, FromValue b) => FromValue (Either a b)
instance (ToValue a, ToValue b) => ToValue (a, b)
instance (FromValue a, FromValue b) => FromValue (a, b)
-- TODO Vector/Set (as []), map as [Entry]








fromValueL :: MonadError String m => (Value -> m b) -> Value -> m [b]
fromValueL fromValue (VList xs) = mapM fromValue xs
fromValueL _         v          = failfromValue "VList" v




fromValueRTh (VRecord m) = return m
fromValueRTh v           = failfromValue "VRecord" v

failfromValue :: MonadError String f => String -> Value -> f a
failfromValue desc v = throwError $ "Expected a " ++ desc ++
    ", but got: " ++ show (ppValue v)






-- TODO for testing...
data V1 a = V1 { s :: a } deriving (G.Generic, Show)
instance (HasType a) => HasType (V1 a)
instance (ToValue a) => ToValue (V1 a)
instance (FromValue a) => FromValue (V1 a)
data V2 a b = V2 { a :: a, b :: b } deriving (G.Generic, Show)
instance (HasType a, HasType b) => HasType (V2 a b)
instance (ToValue a, ToValue b) => ToValue (V2 a b)
instance (FromValue a, FromValue b) => FromValue (V2 a b)
data V3 a b c = V3 { x :: a, y :: b, z :: c } deriving (G.Generic, Show)
instance (HasType a, HasType b, HasType c) => HasType (V3 a b c)
instance (ToValue a, ToValue b, ToValue c) => ToValue (V3 a b c)
instance (FromValue a, FromValue b, FromValue c) => FromValue (V3 a b c)
data V4 a b c d = V4 { m :: a, n :: b, o :: c, p :: d } deriving (G.Generic, Show)
instance (HasType a, HasType b, HasType c, HasType d) => HasType (V4 a b c d)
instance (ToValue a, ToValue b, ToValue c, ToValue d) => ToValue (V4 a b c d)
instance (FromValue a, FromValue b, FromValue c, FromValue d) => FromValue (V4 a b c d)



data Choice0 deriving (G.Generic)
instance HasType Choice0
instance ToValue Choice0
instance FromValue Choice0
data Choice3 a b c = Choice3_1 a | Choice3_2 b | Choice3_3 c deriving (G.Generic, Show)
instance (HasType a, HasType b, HasType c) => HasType (Choice3 a b c)
instance (ToValue a, ToValue b, ToValue c) => ToValue (Choice3 a b c)
instance (FromValue a, FromValue b, FromValue c) => FromValue (Choice3 a b c)

-- TODO test
roundTrip :: (ToValue a, FromValue a) => a -> Either String a
roundTrip = runEvalM' . fromValue . toValue


-- FIXME debug
{- traceV :: Value -> Value -}
{- traceV x = trace (showR . runEvalM' $ ppValue' x) x -}
  where
showR (Right x) = show x
showR (Left e) = "<<Error:" <> show e <> ">>"


