{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- |
-- Module      : Expresso.Eval
-- Copyright   : (c) Tim Williams 2017-2019
-- License     : BSD3
--
-- Maintainer  : info@timphilipwilliams.com
-- Stability   : experimental
-- Portability : portable
--
-- A lazy evaluator.
--
-- The front-end syntax is simple, so we evaluate it directly.
--
module Expresso.Eval(
    Env
  , EvalM
  , HasValue(..)
  , Thunk(..)
  , Value(..)
  , bind
  , eval
  , insertEnv
  , mkStrictLam
  , mkStrictLam2
  , mkStrictLam3
  , mkThunk
  , ppValue
  , ppValue'
  , runEvalM
)
where

import Control.Monad.Except
import Data.Foldable (foldrM)
import Data.HashMap.Strict (HashMap)
import Data.IORef
import Data.Ord
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.HashMap.Strict as HashMap
import qualified Data.List as List

import Expresso.Syntax
import Expresso.Type
import Expresso.Pretty
import Expresso.Utils (cata, (:*:)(..), K(..))

-- | A call-by-need environment.
-- Using a HashMap makes it easy to support record wildcards.
newtype Env = Env { unEnv :: HashMap Name Thunk } deriving (Semigroup, Monoid)

type EvalM a = ExceptT String IO a

-- | A potentially unevaluated value.
newtype Thunk = Thunk { force :: EvalM Value }

instance Show Thunk where
    show _ = "<Thunk>"

mkThunk :: EvalM Value -> EvalM Thunk
mkThunk ev = do
  ref <- liftIO $ newIORef Nothing
  return $ Thunk $ do
      mv <- liftIO $ readIORef ref
      case mv of
          Nothing -> do
              v <- ev
              liftIO $ writeIORef ref (Just v)
              return v
          Just v  -> return v

-- | Type for an evaluated term.
data Value
  = VLam     !(Thunk -> EvalM Value)
  | VInt     !Integer
  | VDbl     !Double
  | VBool    !Bool
  | VChar    !Char
  | VText    !Text
  | VList    ![Value] -- lists are strict
  | VRecord  !(HashMap Label Thunk) -- field order no defined
  | VVariant !Label !Thunk

-- | This does *not* evaluate deeply
ppValue :: Value -> Doc
ppValue (VLam  _)   = "<Lambda>"
ppValue (VInt  i)   = integer i
ppValue (VDbl  d)   = double d
ppValue (VBool b)   = if b then "True" else "False"
ppValue (VChar c)   = text $ '\'' : c : '\'' : []
ppValue (VText s)   = string (show $ T.unpack s)
ppValue (VList xs)  = bracketsList $ map ppValue xs
ppValue (VRecord m) = bracesList $ map ppEntry $ HashMap.keys m
  where
    ppEntry l = text l <+> "=" <+> "<Thunk>"
ppValue (VVariant l _) = text l <+> "<Thunk>"

-- | This evaluates deeply
ppValue' :: Value -> EvalM Doc
ppValue' (VRecord m) = (bracesList . map ppEntry . HashMap.toList)
                           <$> mapM (force >=> ppValue') m
  where
    ppEntry (l, v) = text l <+> text "=" <+> v
ppValue' (VVariant l t) = (text l <+>) <$> (force >=> ppParensValue) t
ppValue' v = return $ ppValue v

ppParensValue :: Value -> EvalM Doc
ppParensValue v =
    case v of
        VVariant{} -> parens <$> ppValue' v
        _          -> ppValue' v

extractChar :: Value -> Maybe Char
extractChar (VChar c) = Just c
extractChar _ = Nothing

-- | Run the EvalM evaluation computation.
runEvalM :: EvalM a -> IO (Either String a)
runEvalM = runExceptT

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
    Text s        -> VText s
    Show          -> mkStrictLam $ \v -> VText . T.pack . show <$> ppValue' v
    -- Trace
    ErrorPrim     -> VLam $ \s -> do
        msg <- proj' s
        throwError $ "error (" ++ show pos ++ "): " ++ msg

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

    Not           -> VLam $ \v -> VBool <$> proj' v
    And           -> VLam $ \v1 -> return $ VLam $ \v2 ->
        VBool <$> ((&&) <$> proj' v1 <*> proj' v2)

    Or            -> VLam $ \v1 -> return $ VLam $ \v2 ->
        VBool <$> ((||) <$> proj' v1 <*> proj' v2)

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
        proj' c >>= \c -> if c then force t else force f
    FixPrim       -> mkStrictLam $ \f -> fix (evalApp pos f <=< mkThunk)

    -- We cannot yet define operators like this in the language
    FwdComp       -> mkStrictLam2 $ \f g ->
        return $ VLam $ \x ->
            mkThunk (evalApp pos f x) >>= evalApp pos g
    BwdComp    -> mkStrictLam2 $ \f g ->
        return $ VLam $ \x ->
            mkThunk (evalApp pos g x) >>= evalApp pos f

    Pack          -> mkStrictLam $ packChars pos
    Unpack        -> mkStrictLam $ unpackChars pos

    ListEmpty     -> VList []
    ListNull      -> VLam $ \xs ->
        (VBool . (null :: [Value] -> Bool)) <$> proj' xs
    ListCons      -> VLam $ \x -> return $ VLam $ \xs ->
        VList <$> ((:) <$> force x <*> proj' xs)
    ListAppend    -> VLam $ \xs -> return $ VLam $ \ys ->
        VList <$> ((++) <$> proj' xs <*> proj' ys)
    ListFoldr     -> mkStrictLam $ \f ->
        return $ VLam $ \z -> return $ VLam $ \xs -> do
        let g a b = do g' <- evalApp pos f (Thunk $ return a)
                       evalApp pos g' (Thunk $ return b)
        z'  <- force z
        xs' <- proj' xs :: EvalM [Value]
        foldrM g z' xs'

    RecordExtend l   -> VLam $ \v -> return $ VLam $ \r ->
        (VRecord . HashMap.insert l v) <$> proj' r
    RecordRestrict l -> VLam $ \r ->
        (VRecord . HashMap.delete l) <$> proj' r
    RecordSelect l   -> VLam $ \r -> do
        r' <- proj' r
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
    Arg n -> return $ insertEnv n t env
    _     -> bind' env b t

-- strict bind
bind' :: Env -> Bind Name -> Thunk -> EvalM Env
bind' env b t = do
  v <- force t
  case (b, v) of
    (Arg n, _)               ->
        return $ insertEnv n (Thunk $ return v) env
    (RecArg ns, VRecord m) | Just vs <- mapM (\n -> HashMap.lookup n m) ns ->
        return $ env <> (mkEnv $ zip ns vs)
    (RecWildcard, VRecord m) ->
        return $ env <> Env m
    _ -> throwError $ "Cannot bind the pair: " ++ show b ++ " = " ++ show (ppValue v)

insertEnv :: Name -> Thunk -> Env -> Env
insertEnv n t (Env m) = Env $ HashMap.insert n t m

lookupEnv :: Name -> Env -> Maybe Thunk
lookupEnv n (Env m) = HashMap.lookup n m

mkEnv :: [(Name, Thunk)] -> Env
mkEnv = Env . HashMap.fromList

lookupValue :: Env -> Name -> EvalM Thunk
lookupValue env n = maybe err return $ lookupEnv n env
  where
    err = throwError $ "Not found: " ++ show n

failOnValues :: Pos -> [Value] -> EvalM a
failOnValues pos vs = throwError $ show pos ++ " : Unexpected value(s) : " ++
                                   show (parensList (map ppValue vs))

-- | Make a strict Expresso lambda value (forced arguments) from a
-- Haskell lambda.
mkStrictLam :: (Value -> EvalM Value) -> Value
mkStrictLam f = VLam $ \x -> force x >>= f

-- | As mkStrictLam, but accepts Haskell functions with two curried arguments.
mkStrictLam2 :: (Value -> Value -> EvalM Value) -> Value
mkStrictLam2 f = mkStrictLam $ \v -> return $ mkStrictLam $ f v

-- | As mkStrictLam, but accepts Haskell functions with three curried arguments.
mkStrictLam3 :: (Value -> Value -> Value -> EvalM Value) -> Value
mkStrictLam3 f = mkStrictLam $ \v -> return $ mkStrictLam2 $ f v

proj' :: HasValue a => Thunk -> EvalM a
proj' = force >=> proj

numOp :: Pos -> (forall a. Num a => a -> a -> a) -> Value -> Value -> EvalM Value
numOp _ op (VInt x) (VInt y) = return $ VInt $ x `op` y
numOp _ op (VDbl x) (VDbl y) = return $ VDbl $ x `op` y
numOp p _  v1       v2       = failOnValues p [v1, v2]

-- NB: evaluates deeply
equalValues :: Pos -> Value -> Value -> EvalM Bool
equalValues _ (VInt i1)  (VInt i2)  = return $ i1 == i2
equalValues _ (VDbl d1)  (VDbl d2)  = return $ d1 == d2
equalValues _ (VBool b1) (VBool b2) = return $ b1 == b2
equalValues _ (VChar c1) (VChar c2) = return $ c1 == c2
equalValues _ (VText s1) (VText s2) = return $ s1 == s2
equalValues p (VList xs) (VList ys)
    | length xs == length ys = and <$> zipWithM (equalValues p) xs ys
    | otherwise = return False
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
compareValues _ (VInt i1)  (VInt i2)  = return $ compare i1 i2
compareValues _ (VDbl d1)  (VDbl d2)  = return $ compare d1 d2
compareValues _ (VBool b1) (VBool b2) = return $ compare b1 b2
compareValues _ (VChar c1) (VChar c2) = return $ compare c1 c2
compareValues _ (VText s1) (VText s2) = return $ compare s1 s2
compareValues p (VList xs) (VList ys) = go xs ys
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
compareValues p v1 v2 = failOnValues p [v1, v2]

-- | Used for equality of records, sorts values by key
recordValues :: HashMap Label a -> [(Label, a)]
recordValues = List.sortBy (comparing fst) . HashMap.toList

packChars :: Pos -> Value -> EvalM Value
packChars pos (VList xs)
    | Just cs <- mapM extractChar xs = return . VText . T.pack $ cs
    | otherwise = failOnValues pos xs
packChars pos v = failOnValues pos [v]

unpackChars :: Pos -> Value -> EvalM Value
unpackChars _   (VText s) = return . VList . map VChar . T.unpack $ s
unpackChars pos v = failOnValues pos [v]

------------------------------------------------------------
-- HasValue class and instances

-- TODO generic derivation a la GG

-- TODO write pure evaluator in ST, carry type in class to get rid of Either/Maybe to get
--    instance (HasValue b) => HasValue (a -> b) where
instance (HasValue a, HasValue b) => HasValue (a -> EvalM b) where
    proj (VLam f) = return $ \x -> do
      r <- f (Thunk $ return $ inj x)
      proj r
    proj v        = failProj "VLam" v
    inj f         = VLam $ \v -> proj' v >>= fmap inj . f

-- | A class of Haskell types that can be projected from or injected
-- into Expresso values.
class HasValue a where
    proj :: Value -> EvalM a
    inj  :: a -> Value

instance HasValue Value where
    proj v        = return v
    inj           = id

instance HasValue Integer where
    proj (VInt i) = return i
    proj v        = failProj "VInt" v
    inj           = VInt

instance HasValue Double where
    proj (VDbl d) = return d
    proj v        = failProj "VDbl" v
    inj           = VDbl

instance HasValue Bool where
    proj (VBool b) = return b
    proj v         = failProj "VBool" v
    inj            = VBool

instance HasValue Char where
    proj (VChar c) = return c
    proj v         = failProj "VChar" v
    inj            = VChar

instance HasValue Text where
    proj (VText s) = return s
    proj v         = failProj "VText" v
    inj            = VText

instance {-# OVERLAPS #-} HasValue a => HasValue [a] where
    proj (VList xs) = mapM proj xs
    proj v          = failProj "VList" v
    inj             = VList . map inj

instance {-# OVERLAPS #-} HasValue [Value] where
    proj (VList xs)  = return xs
    proj v           = failProj "VList" v
    inj              = VList

instance HasValue a => HasValue (HashMap Name a) where
    proj (VRecord m) = mapM proj' m
    proj v           = failProj "VRecord" v
    inj              = VRecord . fmap (Thunk . return . inj)

instance {-# OVERLAPS #-} HasValue a => HasValue [(Name, a)] where
    proj v           = HashMap.toList <$> proj v
    inj              = inj . HashMap.fromList

instance {-# OVERLAPS #-} HasValue (HashMap Name Thunk) where
    proj (VRecord m) = return m
    proj v           = failProj "VRecord" v
    inj              = VRecord

instance {-# OVERLAPS #-} HasValue [(Name, Thunk)] where
    proj v           = HashMap.toList <$> proj v
    inj              = inj . HashMap.fromList

failProj :: String -> Value -> EvalM a
failProj desc v = throwError $ "Expected a " ++ desc ++
    ", but got: " ++ show (ppValue v)
