
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import GHC.Generics
import GHC.TypeLits
import Data.Proxy
import Data.Void
import Data.Map (Map)
import Control.Monad.Error

import Data.Vinyl

import Expresso hiding (typeOf) -- TODO resolve conflict
-- TODO reexport
import Expresso.Eval

main = defaultMain unitTests

unitTests = testGroup
  "End-to-end functional tests"
  [ letTests
  , lambdaTests
  , recordTests
  , variantTests
  , listTests
  , relationalTests
  , constraintTests
  , rankNTests

  , foreignTypeTests
  , foreignImportTests
  , foreignExportTests

  , lazyTests
  ]

letTests = testGroup
  "Let expressions"
  [ hasValue "let x = 1 in x" (1::Integer)
  , hasValue "let x = 1 in let y = 2 in x + y" (3::Integer)
  , hasValue "let x = 1; y = 2 in x + y" (3::Integer)

  {- , hasValue "let {..} = {inc = \\x -> x + 1} in inc 1" (2::Integer) -}
  {- , hasValue "let m = {inc = \\x -> x + 1} in m.inc 1" (2::Integer) -}

  {- , hasValue "let m = {id = \\x -> x} in {foo = [m.id 1], bar = m.id [1]}" -}
        {- $ toMap ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])] -}

  {- -- Record argument field-pun generalisation -}
  {- , hasValue "let {id} = {id = \\x -> x} in {foo = [id 1], bar = id [1]}" -}
        {- $ toMap ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])] -}
  {- , hasValue "let {..} = {id = \\x -> x} in {foo = [id 1], bar = id [1]}" -}
        {- $ toMap ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])] -}

    {- -- Num constraint violation -}
  {- , illTyped "let square = \\x -> x * x in {foo = square 1, bar = square [1]}" -}

  , hasValue "let {..} = {inc = x -> x + 1} in inc 1" (2::Integer)
  , hasValue "let m = {inc = x -> x + 1} in m.inc 1" (2::Integer)

  , hasValue "let m = {id = x -> x} in {foo = [m.id 1], bar = m.id [1]}"
        ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])]

  -- Record argument field-pun generalisation
  , hasValue "let {id} = {id = x -> x} in {foo = [id 1], bar = id [1]}"
        ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])]
  , hasValue "let {..} = {id = x -> x} in {foo = [id 1], bar = id [1]}"
        ["foo" --> ([1]::[Integer]), "bar" --> ([1]::[Integer])]

    -- Num constraint violation
  , illTyped "let square = x -> x * x in {foo = square 1, bar = square [1]}"
  ]

lambdaTests = testGroup
  "Lambda expressions"
  [
    {- hasValue "(\\x -> \\y -> x + y) 1 2" (3::Integer) -}
  {- , hasValue "(\\x y -> x + y) 1 2" (3::Integer) -}
  {- , illTyped "\\x -> x x" -}
  {- , illTyped "let absorb = fix (\\r x -> r) in absorb" -}
  {- , illTyped "let create = fix (\\r x -> r x x) in create" -}
  {- ,  -}
    hasValue "(x -> y -> x + y) 1 2" (3::Integer)
  , hasValue "(x y -> x + y) 1 2" (3::Integer)
  , illTyped "x -> x x"
  , illTyped "let absorb = fix (r x -> r) in absorb"
  , illTyped "let create = fix (r x -> r x x) in create"
  ]

recordTests = testGroup
  "Record expressions"
  [ hasValue "(\\{x, y} -> {x, y}) {x=1, y=2}" $ toMap ["x"-->(1::Integer), "y"-->2]
  , hasValue "{x = 1, y = 2}" $ toMap ["x"-->(1::Integer), "y"-->2]
  , hasValue "(\\r -> { x = 1, y = 2 | r}) { z = 3 }" $ toMap ["x"-->(1::Integer), "y"-->2, "z"-->3]
  , hasValue "{ x = { y = { z = 42 }}}.x.y.z" (42::Integer)

  -- Row tail unification soundness
  , illTyped "\\r -> if True then { x = 1 | r } else { y = 2 | r }"

  , hasValue "({x, y} -> {x, y}) {x=1, y=2}" $ toMap ["x"-->(1::Integer), "y"-->2]
  , hasValue "{x = 1, y = 2}" $ toMap ["x"-->(1::Integer), "y"-->2]
  , hasValue "(r -> { x = 1, y = 2 | r}) { z = 3 }" $ toMap ["x"-->(1::Integer), "y"-->2, "z"-->3]
  , hasValue "{ x = { y = { z = 42 }}}.x.y.z" (42::Integer)

  -- Row tail unification soundness
  , illTyped "r -> if True then { x = 1 | r } else { y = 2 | r }"

  , illTyped "{ x = 2, x = 1 }.x" -- fails to typecheck
  , illTyped "{ x = 2 | { x = 1 }}.x" -- fails to typecheck
  , hasValue "{ x := 2, x = 1 }.x" (2::Integer)
  , hasValue "{ x := 2 | { x = 1 }}.x" (2::Integer)
  , hasValue "{| x = 1 |} {}" $ toMap ["x"-->(1::Integer)]
  , hasValue "({| x = 1, y = 2 |} >> {| z = 3 |}) {}" $ toMap ["x"-->(1::Integer), "y"-->2, "z"-->3]
  , hasValue "({| x = 1, y = 2 |} >> {| x := 42 |}) {}" $ toMap ["x"-->(42::Integer), "y"-->2]
  , illTyped "({| x = 1, y = 2 |} << {| x := 42 |}) {}" -- fails to typecheck
  , hasValue "({| x := 42, y = 2 |} << {| x = 1 |}) {}" $ toMap ["x"-->(42::Integer), "y"-->2]

  -- large record
  , hasValue ("{ x = True }.x") True
  , hasValue ("{ x = 2" ++ concat [", x" ++ show n ++ " = 1" | n <- [1..129] ] ++ " }.x") (2::Integer)
  , hasValue "({| x := 42, y = 2 |} << {| x = 1 |}) {}" ["x"-->(42::Integer), "y"-->2]
  ]

variantTests = testGroup
  "Variant expressions"
  [ hasValue "case Foo 1 of { Foo x -> x + 1, Bar {x, y} -> x + y }"   (2::Integer)
  , hasValue "case Bar {x=1, y=2} of { Foo x -> x + 1, Bar {x, y} -> x + y }"   (3::Integer)
  , illTyped "case Baz{} of { Foo x -> x + 1, Bar {x, y} -> x + y }" -- fails to typecheck
  , hasValue "case Baz{} of { Foo x -> x + 1, Bar {x, y} -> x + y | otherwise -> 42 }"  (42::Integer)
  , illTyped "let f = s -> case s of { Foo x -> x + 1, Bar {x, y} -> x + y }; g = s -> f (<|Foo|> s) in g (Foo 1)" -- fails to typecheck
  , hasValue "let f = s -> case s of { Foo x -> x + 1, Bar {x, y} -> x + y }; g = s -> f (<|Foo|> s) in g (Bar{x=1, y=2})" (3::Integer)
  , hasValue "let f = s -> case s of { Foo x -> x + 1, Bar {x, y} -> x + y | otherwise -> 42 }; g = s -> f (<|Foo,Bar|> s) in g (Baz{})"  (42::Integer)
  , hasValue "case Foo 1 of { override Foo x -> x + 2 | s -> case s of { Foo x -> x + 1 }}" (3::Integer)
  , hasValue "case Foo 1 of { override Foo x -> x + 2, Foo x -> x + 1 }" (3::Integer)

  -- Fail in empty row case
  , illTyped "x -> case x of { A{} -> 1, B{} -> 2, A{} -> 3 }"
  -- Fail in row var case
  , illTyped "x -> <|A, B, A|> x"
  -- Failed row rewrite due to row constraints
  , illTyped ("let f = x -> case (<|A|> x) of { B{} -> 1, otherwise -> 2 }; " ++
              "let g = x -> case (<|B|> x) of { A{} -> 1, otherwise -> 2 } in " ++
              "x -> f x + f x")
  ]

listTests = testGroup
  "List expressions"
  [ hasValue "[1,2,3]" [1::Integer,2,3]
  , illTyped "[1,True]"
  ]

relationalTests = testGroup
  "Relational expressions"
  [ hasValue "(1 == 2)" False
  , hasValue "1/=2" True
  , illTyped "1 == 2 == 3"
  , hasValue "{x = 1, y = True} == {y = True, x = 1}" True -- field order should not matter
  , illTyped "{x = 1, y = True} > {y = True, x = 1}" -- cannot compare records for ordering
  , illTyped "Foo 1 > Bar{}" -- cannot compare variants for ordering
  , hasValue "[1,2,3] == [1,2,3]" True -- lists can be compared for equality
  , hasValue "[1,2,3] >= [1,2,2]" True -- lists can be compared for ordering
  , hasValue "Just 1 == Just 1" True -- maybe can be compared for equality
  , hasValue "Just 2 >= Just 1" True -- maybe can be compared for ordering
  , hasValue "True&&True"   True
  , hasValue "True||False"  True
  ]

constraintTests = testGroup
  "Constraint violations"
  [ illTyped "show { x = \"test\", y = Just (x -> x) }"
  , illTyped "{ x = 2 } > { x = 1}"
  , illTyped "let f = x y -> x + y in f True False"
  ]


lazyTests = testGroup
  "Lazy evaluation tests using error primitive"
  [ hasValue "maybe (error \"bang!\") (x -> x == 42) (Just 42)" True
  , hasValue "{ x = error \"boom!\", y = 42 }.y" (42::Integer)
  , hasValue "case Bar (error \"fizzle!\") of { Foo{} -> 0 | otherwise -> 42 }" (42::Integer)
  ]


rankNTests = testGroup
  "Rank-N polymorphism"
  [ hasValue
         "let f = \\(g ::: forall a. a -> a) -> {l = g True, r = g 1} in f (\\x -> x) == {l = True, r = 1}" True
  , hasValue
         "let k = \\f g x -> f (g x) in let t = k (\\{} -> True) (\\x -> {}) False in let xx = k (\\a -> {}) (\\x -> {}) in t" True

  , hasValue "let f = (g : forall a. a -> a) -> {l = g True, r = g 1} in f (x -> x) == {l = True, r = 1}" True
  , hasValue "let f = g -> {l = g True, r = g 1} : (forall a. a -> a) -> {l : Bool, r : Int } in f (x -> x) == {l = True, r = 1}" True , hasValue "let f = (m : forall a. { reverse : [a] -> [a] |_}) -> {l = m.reverse [True, False], r = m.reverse \"abc\" } in f (import \"Prelude.x\") == {l = [False, True], r = \"cba\"}" True
  -- FIXME breaks due to parser bug
  {- , hasValue -}
         {- "let f = (\\g -> {l = g True, r = g 1}) ::: ((forall a. a -> a) -> {l : Bool, r : Int }) in f (\\x -> x) == {l = True, r = 1}" True -}
  {- , hasValue -}
         {- "let f = \\(m ::: forall a. { reverse : [a] -> [a] |_}) -> {l = m.reverse [True, False], r = m.reverse \"abc\" } in f (import \"Prelude.x\") == {l = [False, True], r = \"cba\"}" True -}
  ]



instance (f ~ ElField) => HasType (Rec f '[]) where
  typeOf _ = _TRecord $ _TRowEmpty
instance (f ~ ElField) => HasType (Rec f ('(k, v) : rs)) where
  typeOf p = _TRecord $ _TRowEmpty

instance (f ~ ElField) => FromValue (Rec f '[]) where
  fromValue _ = pure RNil

instance (f ~ ElField, KnownSymbol k, FromValue v, FromValue (Rec f rs)) => FromValue (Rec f ('(k, v) : rs)) where
  fromValue v = do
    case v of
      VRecord r -> case HashMap.lookup k r of
        Just x -> do
          v <- fromValue =<< force x
          r <- fromValue (VRecord r)
          pure $ rCons kp v r
        Nothing -> throwError $ "bad record, no '" ++ k ++ "'"
      v -> throwError $ "not a record: " ++ show v
    where
      k = symbolVal kp
      kp = (undefined :: F k)


r1 :: FieldRec '[ '("foo", Bool) ]
r1 = (SField :: SField '("foo",Bool)) =: True

r2 :: Rec ElField '[ '("foo", Bool), '("bar", Bool)]
r2 = rec (f::F"foo") True <+> rec (f::F"bar") False


a & b = fi a <+> b
infixr 1 &
infixr 7 ==>

rCons :: KnownSymbol t => proxy t -> a -> FieldRec rs -> FieldRec ('(t, a) : rs)
rCons _ v rs = Field v :& rs

rec :: KnownSymbol t => proxy t -> a -> FieldRec '[ '(t, a) ]
rec _ = (SField =:)

fi :: FI s a -> FieldRec '[ '(s, a) ]
fi (FI x) = SField =: x

data FI :: Symbol -> * -> * where
  FI :: KnownSymbol s => a -> FI s a


(==>) :: KnownSymbol s => F s -> a -> FI s a
_ ==> b = FI b


data F :: Symbol -> * where
f :: F s
f = undefined

-- Marshalling
data Rat = Rat { nom :: Integer, denom :: Integer } | Simple Integer deriving (Generic)

instance HasType Rat
instance FromValue Rat
instance ToValue Rat

newtype ANewType = ANewType { runANewType :: Int } deriving Generic

instance HasType ANewType
instance FromValue ANewType
instance ToValue ANewType

foreignTypeTests = testGroup
  "Foreign types"
  [ hasType (xx :: Proxy Int) "Int"
  , hasType (xx :: Proxy Integer) "Int"
  , hasType (xx :: Proxy Double) "Double"
  , hasType (xx :: Proxy [(Int,Bool)])
      "[{_1 : Int, _2 : <False : {}, True : {}>}]"
    -- or?:
    -- "[(Int,Bool)]"
  -- TODO support Char?
  -- TODO add Text
  , doesNotHaveType (xx :: Proxy Int) "Bool"

  , hasType (xx :: Proxy ()) "{}"
  , hasType (xx :: Proxy Void) "<>"
  , hasType (xx :: Proxy (Either () ())) "<Left : {}, Right : {}>"
  , hasType (xx :: Proxy (Maybe Int)) "<Just : Int, Nothing : {}>"
  {- , hasType (xx :: Proxy (Map String Bool)) "" -} -- TODO add maps as [{key:k,value:v)]
  , hasType (xx :: Proxy (Ordering)) "<EQ : {}, GT : {}, LT : {}>"
  , hasType (xx :: Proxy (Rat)) "<Rat : {denom : Int, nom : Int}, Simple : Int>"

  -- TODO treat ANewType as <ANewType : Int> instead?
  --
  -- No: This complicates the representation of things isomorphic to (), (a,b) etc
  -- Tagging can easily be provided by overriding HasType anyway
  , hasType (xx :: Proxy (ANewType)) "Int"

  , hasType (xx :: Proxy ((Int -> Void) -> Double)) "(Int -> <>) -> Double"
  ]

foreignImportTests = testGroup
  "Foreign import (Haskell to Expresso)"
  [ isValue "1" (1 :: Int)
  , isValue "1" (1 :: Integer)
  , isValue "True" True
  , isValue "2.5" (2.5 :: Double)
  , isValue "\"hello\"" "hello"
  , isValue "{}" ()
  , isValue "Just 2" (Just (2 :: Int))
  ]

foreignExportTests = testGroup
  "Foreign export (Expresso to Haskell)"
  [ hasValue "1" (1 :: Int)
  , hasValue "1" (1 :: Integer)
  , hasValue "True" True
  , hasValue "2.5" (2.5 :: Double)
  , hasValue "\"hello\"" "hello"
  , hasValue "{}" ()
  , hasValue "Just 2" (Just (2 :: Int))


  -- Mono id function
  , hasValueF "x -> x" (2 :: Int) (2 :: Int)
  ]

xx :: Proxy a
xx = error "Do not evaluate"

hasType :: HasType a => Proxy a -> String -> TestTree
hasType hsTy expected = testCase caseStr $
  assertEqual "" expected (show $ ppType $ typeOf hsTy)
  where
    caseStr = show hsTy ++ " " ++ show expected

doesNotHaveType :: HasType a => Proxy a -> String -> TestTree
doesNotHaveType hsTy expected = testCase caseStr $
  if expected == actual
    then assertFailure $ "The Haskell type " ++ expected ++ " should not correspond to " ++ actual
    else assertTrue
  where
    actual = show $ ppType $ typeOf hsTy
    caseStr = show hsTy ++ " " ++ show expected

-- | Test that a given HS value can be imported to Expresso.
isValue :: ToValue a => String -> a -> TestTree
isValue expected hsVal = testCase caseStr $
  assertEqual "" expected actual
  where
    actual = show $ ppValue $ toValue hsVal
    caseStr = expected


-- | Test that a given Expresso expression can be evaluated and exported to Haskell.
hasValue :: (Eq a, Show a, FromValue a) => String -> a -> TestTree
hasValue str = hasValue' str id


-- | Test that a given Expresso expected evalutates to a function, which when applied
-- to the given value returns the given result.
hasValueF :: (Eq b, Show b, FromValue (a -> b)) => String -> a -> b -> TestTree
hasValueF str arg = hasValue' str ($ arg)

hasValue' :: (Eq b, Show b, FromValue a) => String -> (a -> b) -> b -> TestTree
hasValue' str f expected = testCase str $ do
    result <- evalString str
    case result of
        Left err     -> assertFailure err
        Right x      -> let actual = f x in assertEqual "" expected actual

illTyped :: String -> TestTree
illTyped str = testCase str $ do
    sch'e <- typeOfString str
    case sch'e of
        Left _    -> assertTrue
        Right sch -> assertFailure $ "Should not type-check, but got: " ++ showType sch

assertTrue = return ()

(-->) :: FromValue a => Name -> a -> (Name, a)
(-->) l v = (l, v)

toMap :: (Eq a, Show a, FromValue a) => [(Name, a)] -> HashMap Name a
toMap = HashMap.fromList
