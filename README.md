# Polytyped - Alternative to `Dynamic` with type guarantees

With `Dynamic` you can store a value of any type in the same container,
but you have to track manually what kind of types can possibly be inside.

```hs
import Data.Dynamic
import Data.MysteryBox (getSomeDynamic)

main :: IO ()
main = do
  let dyn = getSomeDynamic
  -- getSomeDynamic :: Dynamic
  putStrLn $ show ((fromDynamic dyn) :: a?) -- What type can this possibly be?
```

`Poly` carries this information in a type level list, so you can be sure that
it's container contains a value of one of those types.

```hs
import Data.Polytyped
import Data.MysteryBox (getSomePoly)

main :: IO ()
main = do
  let poly = getSomePoly
  -- getSomePoly :: Poly '[Car, Bike, Goat, Money]
  putStrLn $ show ((fromPoly poly) :: Car) -- This is no longer a guesswork.
```

`Poly` supplies a similar function as custom sum-type without actually needing to define
the type. However unlike sum-types, you can't have two different constructors that contain
the same type.
