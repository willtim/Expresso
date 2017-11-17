{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}

------------------------------------------------------------
--
-- A lazy evaluator
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
import Data.Monoid
import qualified Data.HashMap.Strict as HashMap

import Expresso.Syntax
import Expresso.Pretty
import Expresso.Utils (cata, second)

-- call-by-need environment
-- A HashMap makes it easy to support record wildcards
type Env = HashMap Name Thunk

type EvalM a = ExceptT String IO a

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

data Value
  = VLam     !(Thunk -> EvalM Value)
  | VInt     !Integer
  | VBool    !Bool
  | VChar    !Char
  | VString  !String  -- an optimisation
  | VList    ![Value] -- lists are strict
  | VRecord  !(HashMap Label Thunk)
  | VVariant !Label !Thunk

-- | This does *not* evaluate deeply
ppValue :: Value -> Doc
ppValue (VLam  _)   = "<Lambda>"
ppValue (VInt  i)   = integer i
ppValue (VBool b)   = if b then "True" else "False"
ppValue (VChar c)   = text $ c : []
ppValue (VString s) = dquotes $ text s
ppValue (VList xs)
    | Just str <- mapM extractChar xs = dquotes $ text str
    | otherwise       = bracketsList $ map ppValue xs
ppValue (VRecord r) = bracesList $ map ppEntry $ HashMap.toList r
  where
    ppEntry (l, _) = text l <+> "=" <+> "<Thunk>"
ppValue (VVariant l _) = text l <+> "<Thunk>"

-- | This evaluates deeply
ppValue' :: Value -> EvalM Doc
ppValue' (VRecord m) = (braces . sepBy comma . map ppEntry . HashMap.toList)
                       <$> mapM (force >=> ppValue') m
  where
    ppEntry (l, v) = text l <+> text "=" <+> v
ppValue' (VVariant l t) = (text l <+>) <$> (force >=> ppValue') t
ppValue' v = return $ ppValue v

extractChar :: Value -> Maybe Char
extractChar (VChar c) = Just c
extractChar _ = Nothing

runEvalM :: EvalM a -> IO (Either String a)
runEvalM = runExceptT

eval :: Env -> Exp -> EvalM Value
eval env (stripPos -> e) = cata alg e env
  where
    alg :: ExpF Name Bind (Env -> EvalM Value) -> Env -> EvalM Value
    alg (EVar v)       env = lookupValue env v >>= force
    alg (EApp f x)     env = do
        f' <- f env
        x' <- mkThunk (x env)
        evalApp f' x'
    alg (ELam b e1)    env = return $ VLam $ \x ->
        bind env b x >>= e1
    alg (ELet b e1 e2) env = do
        t    <- mkThunk $ e1 env
        env' <- bind env b t
        e2 env'
    -- alg (LetRec bs e2) env =
    --   e2 $ fix $ \env' ->
    --     let f (b, e1) env'' = bind env'' b (e1 env')
    --     in foldr f env bs
    -- alg (Case s alts)  env = evalCase (s env) alts env
    alg (EPrim p)      _   = return $ evalPrim p

evalApp :: Value -> Thunk -> EvalM Value
evalApp (VLam f)   t  = f t
evalApp fv         _  = throwError $ "Expected a function, but got: " ++ show (ppValue fv)

evalPrim :: Prim -> Value
evalPrim p = case p of
    Int i    -> VInt i
    Bool b   -> VBool b
    Char c   -> VChar c
    String s -> VString s
    -- Trace    -> VLam $ \s -> VLam $ \x ->
    ErrorPrim -> VLam $ \s -> do
        msg <- proj' s
        throwError $ "error: " ++ msg
    Neg      -> VLam $ \x ->
        VInt <$> (negate <$> proj' x)
    Add      -> binOp VInt (+)
    Sub      -> binOp VInt (-)
    Mul      -> binOp VInt (*)
    Div      -> binOp VInt div
    Cond     -> VLam $ \c -> return $ VLam $ \t -> return $ VLam $ \f ->
        proj' c >>= \c -> if c then force t else force f
    FixPrim    -> VLam $ \f -> force f >>= \f' -> fix (evalApp f' <=< mkThunk)

    -- We cannot yet define operators like this in the language
    FwdComp    -> VLam $ \f -> force f >>= \f' ->
                  return $ VLam $ \g -> force g >>= \g' ->
                  return $ VLam $ \x ->
                      mkThunk (evalApp f' x) >>= evalApp g'
    BwdComp    -> VLam $ \f -> force f >>= \f' ->
                  return $ VLam $ \g -> force g >>= \g' ->
                  return $ VLam $ \x ->
                      mkThunk (evalApp g' x) >>= evalApp f'
    ListEmpty  -> VList []
    ListNull   -> VLam $ \xs -> -- TODO
        (VBool . (null :: [Value] -> Bool)) <$> proj' xs
    ListCons   -> VLam $ \x -> return $ VLam $ \xs ->
        VList <$> ((:) <$> force x <*> proj' xs)
    -- ListUncons -> VLam $ \xs ->
    --     let xs' = proj xs
    --     in either VErr VTuple ((\x xs -> [x, inj xs]) <$> (head <$> xs') <*> (tail <$> xs'))
    ListAppend -> VLam $ \xs -> return $ VLam $ \ys ->
        VList <$> ((++) <$> proj' xs <*> proj' ys)
    ListFoldr  -> VLam $ \f -> return $ VLam $ \z -> return $ VLam $ \xs -> do
        let g a b = do f' <- force f
                       g  <- evalApp f' (Thunk $ return a)
                       evalApp g (Thunk $ return b)
        z'  <- force z
        xs' <- proj' xs :: EvalM [Value]
        foldrM g z' xs'
    RecordExtend l -> VLam $ \v -> return $ VLam $ \r ->
        (VRecord . HashMap.insert l v) <$> proj' r
    RecordRestrict l -> VLam $ \r ->
        (VRecord . HashMap.delete l) <$> proj' r
    RecordSelect l -> VLam $ \r -> do
        r' <- proj' r
        maybe (throwError $ l ++ " not found") force (HashMap.lookup l r')
    RecordEmpty -> VRecord mempty
    VariantInject l -> VLam $ \v ->
        return $ VVariant l v
    VariantEmbed _  -> VLam $ \v -> force v
    VariantElim l   -> VLam $ \f -> return $ VLam $ \k -> return $ VLam $ \s -> do
        f' <- force f
        k' <- force k
        s' <- force s
        case s' of
            VVariant l' t | l==l'     -> evalApp f' t
                          | otherwise -> evalApp k' s
            v -> throwError $ "Expected a variant, but got: " ++ show (ppValue v)
    p -> error $ "Unsupported Prim: " ++ show p

binOp :: HasValue a => (a -> Value) -> (a -> a -> a) -> Value
binOp c op = VLam $ \x -> return $ VLam $ \y ->
    c <$> (op <$> proj' x <*> proj' y)

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
    (RecArg ns, VRecord m) | Just vs <- mapM (`HashMap.lookup` m) ns ->
        return $ env <> (HashMap.fromList $ zip ns vs)
    (RecWildcard, VRecord m) ->
        return $ env <> m
    _ -> throwError $ "Cannot bind the pair: " ++ show b ++ " = " ++ show (ppValue v)

lookupValue :: Env -> Name -> EvalM Thunk
lookupValue env n = maybe err return $ HashMap.lookup n env
  where
    err = throwError $ "Not found: " ++ show n

------------------------------------------------------------
-- HasValue class and instances

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

instance HasValue Bool where
    proj (VBool b) = return b
    proj v         = failProj "VBool" v
    inj            = VBool

instance HasValue Char where
    proj (VChar c) = return c
    proj v         = failProj "VChar" v
    inj            = VChar

instance {-# OVERLAPS #-} HasValue String where
    proj (VString s) = return s
    proj v           = failProj "VString" v
    inj              = VString

instance HasValue a => HasValue [a] where
    proj (VList xs) = mapM proj xs
    proj v          = failProj "VList" v
    inj             = VList . map inj

instance {-# OVERLAPS #-} HasValue [Value] where
    proj (VList xs)  = return xs
    proj (VString s) = return $ map VChar s
    proj v           = failProj "VList" v
    inj              = VList

instance HasValue a => HasValue (HashMap Name a) where
    proj (VRecord m) = mapM proj' m
    proj v           = failProj "VRecord" v
    inj              = VRecord . fmap (Thunk . return . inj)

instance {-# OVERLAPS #-} HasValue a => HasValue [(Name, a)] where
    proj (VRecord m) = mapM (mapM proj') $ HashMap.toList m
    proj v           = failProj "VRecord" v
    inj              = VRecord . HashMap.fromList . map (second $ Thunk . return . inj)

instance {-# OVERLAPS #-} HasValue (HashMap Name Thunk) where
    proj (VRecord m) = return m
    proj v           = failProj "VRecord" v
    inj              = VRecord

instance {-# OVERLAPS #-} HasValue [(Name, Thunk)] where
    proj (VRecord m) = return $ HashMap.toList m
    proj v           = failProj "VRecord" v
    inj              = VRecord . HashMap.fromList

proj' :: HasValue a => Thunk -> EvalM a
proj' = force >=> proj

failProj :: String -> Value -> EvalM a
failProj desc v = throwError $ "Expected a " ++ desc ++ ", but got: " ++ show (ppValue v)
