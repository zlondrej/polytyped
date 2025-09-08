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
it contains a value of one of the listed types.

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
the type. However unlike sum-types, `Poly` doesn't allow specifying same type multiple times.
Representing type such as `SumOp` is not possible.

```hs
data SumOp
  = Add Int
  | Sub Int
```

You will need to help the type system by using tagged types:

```hs

import Data.Tagged

data AddOp
data SubOp

-- Representation of `SumOp` sum-type with `Poly` and tagged types.
type MyTaggedPoly = Poly '[Tagged AddOp Int, Tagged SubOpInt]
```

or newtype wrappers:

```hs

newtype AddOp = Add Int
newtype SubOp = Sub Int

-- Representation of `SumOp` sum-type with `Poly` and newtypes.
type MyNewtypePoly = Poly '[AddOp, SubOp]
```