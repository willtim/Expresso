{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}

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
  , HasValue(..)
  , Value(..)
  , ppValue
  , ppValue'
  , force
  , mkThunk
  , bind
)
where

import Control.Monad.Except
import Data.Foldable (foldrM)
import Data.HashMap.Strict (HashMap)
import Data.IORef
import Data.Coerce
import Data.Maybe
import Data.Monoid
import qualified Data.HashMap.Strict as HashMap
import qualified Data.List as List
import Control.Monad.ST
import Data.STRef
import Data.Void
import Data.Functor.Identity

import Expresso.Syntax
import Expresso.Type
import Expresso.Pretty
import Expresso.Utils (cata, (:*:)(..), K(..))

-- call-by-need environment
-- A HashMap makes it easy to support record wildcards
type Env = HashMap Name Thunk

newtype EvalM a = EvalM { runEvalT :: ExceptT String Identity a }
instance Functor EvalM
instance Applicative EvalM
instance Monad EvalM
instance MonadError String EvalM

newtype Thunk = Thunk { force :: EvalM Value }

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
  | VString  !String  -- an optimisation
  | VMaybe   !(Maybe Value)
  | VList    ![Value] -- lists are strict
  | VRecord  ![Label] !(HashMap Label Thunk) -- maintain field order
  | VVariant !Label !Thunk

-- | This does *not* evaluate deeply
ppValue :: Value -> Doc
ppValue (VLam  _)   = "<Lambda>"
ppValue (VInt  i)   = integer i
ppValue (VDbl  d)   = double d
ppValue (VBool b)   = if b then "True" else "False"
ppValue (VChar c)   = text $ c : []
ppValue (VString s) = dquotes $ text s
ppValue (VMaybe mx) = maybe "Nothing" (\v -> "Just" <+> ppValue v) mx
ppValue (VList xs)
    | Just str <- mapM extractChar xs = dquotes $ text str
    | otherwise     = bracketsList $ map ppValue xs
ppValue (VRecord ls _) = bracesList $ map ppEntry ls
  where
    ppEntry l = text l <+> "=" <+> "<Thunk>"
ppValue (VVariant l _) = text l <+> "<Thunk>"

-- | This evaluates deeply
ppValue' :: Value -> EvalM Doc
ppValue' (VRecord ls m) = (bracesList . zipWith ppEntry ls . recordValues ls)
                          <$> mapM (force >=> ppValue') m
  where
    ppEntry l v = text l <+> text "=" <+> v
ppValue' (VVariant l t) = (text l <+>) <$> (force >=> ppValue') t
ppValue' v = return $ ppValue v

extractChar :: Value -> Maybe Char
extractChar (VChar c) = Just c
extractChar _ = Nothing

runEvalM :: EvalM a -> IO (Either String a)
runEvalM = undefined

runEvalM' :: EvalM a -> Either String a
runEvalM' = runIdentity . runExceptT . runEvalT


eval :: Env -> Exp -> EvalM Value
eval env e = cata alg e env
  where
    alg :: (ExpF Name Bind :*: K Pos) (Env -> EvalM Value)
        -> Env
        -> EvalM Value
    alg (EVar v :*: _)       env = lookupValue env v >>= force
    alg (EApp f x :*: K pos) env = do
        f' <- f env
        x' <- mkThunk (x env)
        evalApp pos f' x'
    alg (ELam b e1 :*: _)    env = return $ VLam $ \x ->
        bind env b x >>= e1
    alg (ELet b e1 e2 :*: _) env = do
        t    <- mkThunk $ e1 env
        env' <- bind env b t
        e2 env'
    alg (EPrim p :*: K pos)  _   = return $ evalPrim pos p


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
    String s      -> VString s
    Show          -> mkStrictLam $ \v -> VString . show <$> ppValue' v
    -- Trace
    ErrorPrim     -> VLam $ \s -> do
        msg <- proj' s
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

    Not           -> VLam $ \v -> VBool <$> proj' v

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

    JustPrim      -> mkStrictLam $ \v -> return $ VMaybe (Just v)
    NothingPrim   -> VMaybe Nothing
    MaybePrim     -> VLam $ \x -> return $ mkStrictLam2 $ \f v ->
        case v of
            VMaybe (Just v') -> evalApp pos f (Thunk $ return v')
            VMaybe Nothing   -> force x
            _                -> failOnValues pos [v]

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
    RecordExtend l   -> VLam $ \v -> return $ mkStrictLam $ \r ->
        case r of
          VRecord ls m -> return $ VRecord (l:ls) (HashMap.insert l v m)
          _ -> failOnValues pos [r]
    RecordRestrict l -> mkStrictLam $ \r ->
        case r of
          VRecord ls m -> return $ VRecord (List.delete l ls) (HashMap.delete l m)
          _ -> failOnValues pos [r]
    RecordSelect l   -> VLam $ \r -> do
        r' <- proj' r
        let err = throwError $ show pos ++ " : " ++ l ++ " not found"
        maybe err force (HashMap.lookup l r')
    RecordEmpty -> VRecord [] mempty
    VariantInject l  -> VLam $ \v ->
        return $ VVariant l v
    VariantEmbed _   -> VLam force
    VariantElim l    -> mkStrictLam $ \f -> return $ mkStrictLam2 $ \k s -> do
        case s of
            VVariant l' t | l==l'     -> evalApp pos f t
                          | otherwise -> evalApp pos k (Thunk $ return s)
            v -> throwError $ show pos ++ " : Expected a variant, but got: " ++
                              show (ppValue v)
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
    (RecArg ns, VRecord _ m) ->
        return $ env <> (HashMap.fromList $ zip ns $ recordValues ns m)
    (RecWildcard, VRecord _ m) ->
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

proj' :: HasValue a => Thunk -> EvalM a
proj' = force >=> proj

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
equalValues _ (VString s1) (VString s2) = return $ s1 == s2
equalValues p (VMaybe m1)  (VMaybe m2)  =
    case (m1, m2) of
      (Just v1, Just v2) -> equalValues p v1 v2
      (Nothing, Nothing) -> return True
      _                  -> return False
equalValues p (VList xs)   (VList ys)
    | length xs == length ys = and <$> zipWithM (equalValues p) xs ys
    | otherwise = return False
equalValues p (VRecord ls1 m1) (VRecord ls2 m2)
    | ls1 == ls2 = do
    vs1 <- recordValues ls1 <$> mapM force m1
    vs2 <- recordValues ls2 <$> mapM force m2
    if length vs1 == length vs2
       then and <$> zipWithM (equalValues p) vs1 vs2
       else return False
    | otherwise = return False
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
compareValues _ (VString s1) (VString s2) = return $ compare s1 s2
compareValues p (VMaybe m1)  (VMaybe m2)  =
    case (m1, m2) of
      (Just v1, Just v2) -> compareValues p v1 v2
      (Nothing, Nothing) -> return EQ
      (Nothing, Just{} ) -> return LT
      (Just{} , Nothing) -> return GT
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
compareValues p (VRecord ls1 m1) (VRecord ls2 m2) = do
    vs1 <- recordValues ls1 <$> mapM force m1
    vs2 <- recordValues ls2 <$> mapM force m2
    let c = compare ls1 ls2
    if c == EQ
       then compareValues p (VList vs1) (VList vs2)
       else return c
compareValues p (VVariant l1 v1) (VVariant l2 v2) =
    let c = compare l1 l2
    in if c == EQ
        then join $ compareValues p <$> force v1 <*> force v2
        else return c
compareValues p v1 v2 = failOnValues p [v1, v2]

-- | Used for ordering and pretty-printing of records
recordValues :: [Label] -> HashMap Label a -> [a]
recordValues ls m = fromMaybe err $ mapM (\l -> HashMap.lookup l m) ls
  where
    err = error "recordValues: assertion failed"

------------------------------------------------------------
-- HasValue class and instances

class Inject a where
    inj :: a -> Value
instance Inject Integer where
    inj = VInt
instance Inject Double where
    inj = VDbl
instance Inject Char where
    inj = VChar

-- TODO generic derivation a la GG

-- TODO write pure evaluator in ST, carry type in class to get rid of Either/Maybe to get
--    instance (Inject a, HasValue b) => HasValue (a -> b) where
instance (Inject a, HasValue b) => HasValue (a -> Either String b) where
    proj (VLam f) = pure $ \x -> runEvalM' $ do
      x <- (mkThunk $ pure $ inj x)
      r <- f x
      proj r
    -- proj v        = failProj "VLam" v


class HasValue a where
    proj :: Value -> EvalM a

instance HasValue Value where
    proj v        = return v

instance HasValue Integer where
    proj (VInt i) = return i
    proj v        = failProj "VInt" v

instance HasValue Double where
    proj (VDbl d) = return d
    proj v        = failProj "VDbl" v

instance HasValue Bool where
    proj (VBool b) = return b
    proj v         = failProj "VBool" v

instance HasValue Char where
    proj (VChar c) = return c
    proj v         = failProj "VChar" v

instance HasValue a => HasValue (Maybe a) where
    proj (VMaybe m) = mapM proj m
    proj v          = failProj "VMaybe" v

instance {-# OVERLAPS #-} HasValue String where
    proj (VString s) = return s
    proj v           = failProj "VString" v

instance HasValue a => HasValue [a] where
    proj (VList xs) = mapM proj xs
    proj v          = failProj "VList" v

instance {-# OVERLAPS #-} HasValue [Value] where
    proj (VList xs)  = return xs
    proj (VString s) = return $ map VChar s
    proj v           = failProj "VList" v

instance HasValue a => HasValue (HashMap Name a) where
    proj (VRecord _ m) = mapM proj' m
    proj v             = failProj "VRecord" v

instance {-# OVERLAPS #-} HasValue a => HasValue [(Name, a)] where
    proj v             = HashMap.toList <$> proj v

instance {-# OVERLAPS #-} HasValue (HashMap Name Thunk) where
    proj (VRecord _ m) = return m
    proj v             = failProj "VRecord" v

instance {-# OVERLAPS #-} HasValue [(Name, Thunk)] where
    proj v             = HashMap.toList <$> proj v

failProj :: String -> Value -> EvalM a
failProj desc v = throwError $ "Expected a " ++ desc ++
    ", but got: " ++ show (ppValue v)
