module Main where

import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertEqual, assertFailure, testCase)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap

import Expresso

main = defaultMain unitTests

unitTests = testGroup
  "End-to-end functional tests"
  [ letTests
  , lambdaTests
  , recordTests
  , variantTests
  , listTests
  ]

letTests = testGroup
  "Let expressions"
  [ hasValue "let x = 1 in x" (1::Integer)
  , hasValue "let x = 1 in let y = 2 in x + y" (3::Integer)
  , hasValue "let x = 1; y = 2 in x + y" (3::Integer)
  , hasValue "let {..} = {inc = x: x + 1} in inc 1" (2::Integer)
  , hasValue "let m = {inc = x: x + 1} in m.inc 1" (2::Integer)
--  , hasValue "let {..} = {id = x: x} in {foo = id 1, bar = id [1]}"
--        ["foo" --> inj (1::Integer), "bar" --> inj ([1]::[Integer])]
--  , hasValue "let m = {id = x: x + 1} in {foo = m.id 1, bar = m.id [1]}"
--        ["foo" --> inj (1::Integer), "bar" --> inj ([1]::[Integer])]
  ]

lambdaTests = testGroup
  "Lambda expressions"
  [ hasValue "(x: y: x + y) 1 2" (3::Integer)
  , illtyped "x: x x"
  , illtyped "let absorb = fix (r: x: r) in absorb"
  , illtyped "let create = fix (r: x: r x x) in create"
  ]

recordTests = testGroup
  "Record expressions"
  [ hasValue "({x, y}: {x, y}) {x=1, y=2}" $ toMap ["x"-->(1::Integer), "y"-->2]
  , hasValue "{x = 1, y = 2}" $ toMap ["x"-->(1::Integer), "y"-->2]
  , hasValue "(x: { x = 1, y = 2 | x}) { z = 3 }" $ toMap ["x"-->(1::Integer), "y"-->2, "z"-->3]
  , hasValue "{ x = { y = { z = 42 }}}.x.y.z" (42::Integer)
  , illtyped "{ x = 2, x = 1 }.x" -- fails to typecheck
  , illtyped "{ x = 2 | { x = 1 }}.x" -- fails to typecheck
  , hasValue "{ x := 2, x = 1 }.x" (2::Integer)
  , hasValue "{ x := 2 | { x = 1 }}.x" (2::Integer)
  , hasValue "{| x = 1 |} {}" $ toMap ["x"-->(1::Integer)]
  , hasValue "({| x = 1, y = 2 |} >> {| z = 3 |}) {}" $ toMap ["x"-->(1::Integer), "y"-->2, "z"-->3]
  , hasValue "({| x = 1, y = 2 |} >> {| x := 42 |}) {}" $ toMap ["x"-->(42::Integer), "y"-->2]
  , illtyped "({| x = 1, y = 2 |} << {| x: = 42 |}) {}" -- fails to typecheck
  , hasValue "({| x := 42, y = 2 |} << {| x = 1 |}) {}" ["x"-->(42::Integer), "y"-->2]
  ]

variantTests = testGroup
  "Variant expressions"
  [ hasValue "case Foo 1 { Foo x: x + 1, Bar {x, y}: x + y }"   (2::Integer)
  , hasValue "case Bar {x=1, y=2} { Foo x: x + 1, Bar {x, y}: x + y }"   (3::Integer)
  , illtyped "case Baz{} { Foo x: x + 1, Bar {x, y}: x + y }" -- fails to typecheck
  , hasValue "case Baz{} { Foo x: x + 1, Bar {x, y}: x + y | otherwise: 42 }"  (42::Integer)
  , illtyped "let f = s: case s { Foo x: x + 1, Bar {x, y}: x + y }; g = s: f <Foo|s> in g Foo 1" -- fails to typecheck
  , hasValue "let f = s: case s { Foo x: x + 1, Bar {x, y}: x + y }; g = s: f <Foo|s> in g Bar {x=1, y=2}" (3::Integer)
  , hasValue "let f = s: case s { Foo x: x + 1, Bar {x, y}: x + y | otherwise: 42 }; g = s: f <Foo,Bar|s> in g Baz{}"  (42::Integer)
  , hasValue "case Foo 1 { override Foo x: x + 2 | s: case s { Foo x: x + 1 }}" (3::Integer)
  , hasValue "case Foo 1 { override Foo x: x + 2, Foo x: x + 1 }" (3::Integer)
  ]

listTests = testGroup
  "List expressions"
  [ hasValue "[1,2,3]" [1::Integer,2,3]
  , illtyped "[1,True]"
  -- "x: y: [x, y]"
  ]

hasValue :: (Eq a, Show a, HasValue a) => String -> a -> TestTree
hasValue str expected = testCase str $ do
    result <- evalString str
    case result of
        Left err     -> assertFailure err
        Right actual -> assertEqual "" expected actual

illtyped :: String -> TestTree
illtyped str = testCase str $ do
    sch'e <- typeOfString str
    case sch'e of
        Left _    -> assertTrue
        Right sch -> assertFailure $ "Should not type-check, but got: " ++ showType sch

assertTrue = return ()

(-->) :: HasValue a => Name -> a -> (Name, a)
(-->) l v = (l, v)

toMap :: (Eq a, Show a, HasValue a) => [(Name, a)] -> HashMap Name a
toMap = HashMap.fromList
