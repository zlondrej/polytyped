{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Data.List
import Data.Polytyped
import Data.Void
import GHC.Generics
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

data Primitive
  = Int Int
  | Word Word
  | String String
  | Bool Bool
  deriving stock (Show, Eq, Ord, Generic)

instance Arbitrary Primitive where
  arbitrary =
    oneof
      [ Int <$> arbitrary
      , Word <$> arbitrary
      , String <$> arbitrary
      , Bool <$> arbitrary
      ]
  shrink = genericShrink

primitiveToPoly :: Primitive -> Poly '[Int, Word, String, Bool]
primitiveToPoly = \case
  Int a -> toPoly a
  Word a -> toPoly a
  String a -> toPoly a
  Bool a -> toPoly a

-- Same as `primitiveToPoly` but with different order of types.
primitiveToPoly2 :: Primitive -> Poly '[Bool, String, Word, Int]
primitiveToPoly2 = \case
  Int a -> toPoly a
  Word a -> toPoly a
  String a -> toPoly a
  Bool a -> toPoly a

poly2ToPrimitive :: Poly '[Bool, String, Word, Int] -> Primitive
poly2ToPrimitive poly =
  polymap
    poly
    (Bool)
    (String)
    (Word)
    (Int)

-- Function to match the ordering for `Primitive` with
-- `Poly '[Bool, String, Word, Int]`.
primitiveOrdering2 :: Primitive -> (Int, Primitive)
primitiveOrdering2 = \case
  Int b -> (3, Int b)
  Word b -> (2, Word b)
  String b -> (1, String b)
  Bool b -> (0, Bool b)

intToPoly :: Int -> Poly '[Int]
intToPoly = toPoly

showPrimitiveLikePoly :: Primitive -> String
showPrimitiveLikePoly = \case
  Int a -> "Poly (Int; " ++ show a ++ ")"
  Word a -> "Poly (Word; " ++ show a ++ ")"
  -- Compiler doesn't preserve type aliases.
  String a -> "Poly ([Char]; " ++ show a ++ ")"
  Bool a -> "Poly (Bool; " ++ show a ++ ")"

polyToInt :: Poly '[Int] -> Int
polyToInt i = case polycast @Int i of
  Right n -> n
  Left n -> absurd n

type Eithers = Either (Either Int Word) (Either String Bool)

polyToEithers :: Poly '[Int, Word, String, Bool] -> Eithers
polyToEithers poly =
  polymap
    poly
    (Left . Left)
    (Left . Right)
    (Right . Left)
    (Right . Right)

primitiveToEithers :: Primitive -> Eithers
primitiveToEithers = \case
  Int a -> Left (Left a)
  Word a -> Left (Right a)
  String a -> Right (Left a)
  Bool a -> Right (Right a)

main :: IO ()
main =
  defaultMain $
    testGroup
      "Polytyped tests"
      [ testGroup
          "Poly instances"
          [ testGroup
              "Show instance"
              [ testProperty "Should show Poly '[Int]" $ \a -> do
                  show (intToPoly a) === showPrimitiveLikePoly (Int a)
              , testProperty "Should show Poly '[Int, Word, String, Bool]" $ \a -> do
                  show (primitiveToPoly a) === showPrimitiveLikePoly a
              ]
          , testGroup
              "Eq instance"
              [ testProperty "Should equal Poly '[Int]" $ \(a, b) -> (a, b) @?== (intToPoly a, intToPoly b)
              , testProperty "Should not equal Poly '[Int, Word, String, Bool]" $ \(a, b) -> (a, b) @?== (primitiveToPoly a, primitiveToPoly b)
              ]
          , testGroup
              "Ord instance"
              [ testProperty "Should compare Poly '[Int]" $ \(a, b) -> (a, b) @?>< (intToPoly a, intToPoly b)
              , testProperty "Should compare Poly '[Int, Word, String, Bool]" $ \(a, b) -> (a, b) @?>< (primitiveToPoly a, primitiveToPoly b)
              , testProperty "Comparing depends on the order of type list" $ \xs ->
                  (sortOn primitiveOrdering2 xs) === (map poly2ToPrimitive . sort $ map primitiveToPoly2 xs)
              ]
          ]
      , testProperty "Can always polycast back to the type" $ \a ->
          case a of
            Int n -> polycast @Int (primitiveToPoly a) === Right n
            Word n -> polycast @Word (primitiveToPoly a) === Right n
            String s -> polycast @String (primitiveToPoly a) === Right s
            Bool b -> polycast @Bool (primitiveToPoly a) === Right b
      , testProperty "Can polymap to any unified type" $ \xs ->
          let polys = map primitiveToPoly xs
           in map polyToEithers polys === map primitiveToEithers xs
      ]
 where
  (a, b) @?== (c, d) =
    counterexample
      ("(" ++ (show a ++ " == " ++ show b) ++ ")" ++ interpret res ++ "(" ++ (show c ++ " == " ++ show d) ++ ")")
      res
   where
    res = (a == b) == (c == d)

  (a, b) @?>< (c, d) =
    counterexample
      ("(" ++ (show a ++ " `compare` " ++ show b) ++ ")" ++ interpret res ++ "(" ++ (show c ++ " `compare` " ++ show d) ++ ")")
      res
   where
    res = (a `compare` b) == (c `compare` d)

  interpret = \case
    True -> " == "
    False -> " /= "
