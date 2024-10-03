{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Polytyped.Internal where

import Data.Kind
import Data.Polytyped.TypeLevel
import Data.Type.Bool
import Data.Typeable
import Data.Void
import Unsafe.Coerce

data Poly ts where
  Poly :: (Unique ts, OneOf a ts, Typeable a) => a -> Poly ts
  deriving stock (Typeable)

toPoly :: (Unique ts, OneOf a ts, Typeable a) => a -> Poly ts
toPoly = Poly

-- | Re-type `Poly` to include additional types.
-- This can only be used to add types to the list, not to remove them.
rePoly :: (SubsetOf sub super) => Poly sub -> Poly super
-- We're only adding types here which are not present in the original list,
-- so `unsafeCoerce` will do the job, without need to actually re-construct all the values.
rePoly = unsafeCoerce

-- | Type class for casting `Poly` to individual types.
--
-- TODO: Review this comment and choose a new name for `UnifyTypedFilter`.
-- This could be included directly in the `UnifyTypedFilter` class, but because
-- of the type-level issues when casting and removing the types from type list,
-- I decided to keep it separate.
class PolyCast a (ts :: [Type]) where
  type PolyUncasted a ts :: Type
  polycast :: Poly ts -> Either (PolyUncasted a ts) a

instance (Typeable t) => PolyCast t '[t] where
  -- This is `Void` so we can return `Either`.
  -- It would be possible return just `t` here, but that would make it
  -- impossible to use `polycast` in contexts where length of the type list is unknown.
  type PolyUncasted t '[t] = Void
  polycast (Poly f) = case cast f of
    Just a -> Right a
    -- This should never happen as `Poly` can only be constructed
    -- with a value of the type in the list, and so it should always cast.
    Nothing ->
      Left $
        error
          "Failed to cast `Poly` of single possible type, \
          \if this happens, please report a bug."

instance (Typeable t, OneOf t (u : v : ts)) => PolyCast t (u : v : ts) where
  type PolyUncasted t (u : v : ts) = Poly (DropElem t (u : v : ts))
  polycast tf@(Poly f) = case cast f of
    Just a -> Right a
    -- `unsafeCoerce` should be safe here as the `Poly` can only be
    -- constructed with a value of one of the types in the list.
    --
    -- Since we are trying to cast `Poly` to the type in the list,
    -- then failure to cast must mean that the `Poly` is one of the remaining types.
    --
    -- However as I'm unable to pass the type value inside of the `Poly` to the
    -- compiler, the type checker is not satisfied as it can't infer `OneOf` constraint
    -- that's required for the `Poly` to be constructed.
    --
    -- So intead of trying to reconstruct the `Poly` with the remaining types,
    -- I'm simply using `unsafeCoerce` to get around this issue.
    --
    -- In case you figure out how to do this without using `unsafeCoerce`, please let me know.
    -- I'm guessing it's doable by fully unwrapping the `Poly` and then
    -- reconstructing it, but that's way too much work and probably inneficient too.
    Nothing -> Left $ unsafeCoerce tf

-- | Type class for mapping `Poly` into unified `result` type.
class PolyMap (ts :: [Type]) result where
  type PolyMapFn ts result :: Type

  -- | Variadic function to reduce ts to `result` type.
  --
  -- Takes as many `? -> result` functions as there are types in the `ts`
  -- type list in the same order as they are defined in the list.
  polymap :: Poly ts -> PolyMapFn ts result

  -- | Helper function to pass the unification to following type
  -- in the list, consuming another `? -> result` function.
  polypass :: result -> PolyMapFn ts result

instance (Typeable f) => PolyMap '[f] result where
  type PolyMapFn '[f] result = (f -> result) -> result
  polymap somePoly fn = fn $ case polycast @f somePoly of
    Right a -> a
    Left void -> absurd void
  polypass a = const a

instance
  ( Typeable f
  , PolyMap (f1 : fs) result
  ) =>
  PolyMap (f : f1 : fs) result
  where
  type PolyMapFn (f : f1 : fs) result = (f -> result) -> PolyMapFn (f1 : fs) result

  polymap somePoly fn = case polycast @f somePoly of
    Right a -> polypass @(f1 : fs) $ fn a
    Left a -> polymap @(f1 : fs) @result a
  polypass a = const $ polypass @(f1 : fs) a

-- | Type class for mapping type in `Poly` internally.
class PolyFunctor u v (ts :: [Type]) where
  type PolyFunctorResult u v ts :: [Type]
  polyfmap :: (u -> v) -> Poly ts -> Poly (PolyFunctorResult u v ts)

instance (Typeable u, Typeable v) => PolyFunctor u v '[u] where
  type PolyFunctorResult u v '[u] = '[v]
  polyfmap fn somePoly = case polycast @u somePoly of
    Right a -> Poly $ fn a
    Left void -> absurd void

instance
  ( Typeable u
  , Typeable v
  , OneOf u (t : t1 : tn)
  , OneOf v result
  , Unique result
  , PolyFunctor u v (DropElem u (t : t1 : tn))
  , PolyFunctorResult u v (DropElem u (t : t1 : tn)) ~ result
  , If (IsElem v (t : t1 : tn)) (DropElem u (t : t1 : tn)) (ReplaceElem u v (t : t1 : tn)) ~ result
  ) =>
  PolyFunctor u v (t : t1 : tn)
  where
  type PolyFunctorResult u v (t : t1 : tn) = If (IsElem v (t : t1 : tn)) (DropElem u (t : t1 : tn)) (ReplaceElem u v (t : t1 : tn))
  polyfmap fn somePoly = case polycast @u somePoly of
    Right a -> Poly $ fn a
    Left b -> polyfmap fn b

-- Show instance

instance (Typeable t, Show t) => Show (Poly '[t]) where
  show a = case polycast @t a of
    Right a' -> "Poly (" <> show (typeOf a') <> "; " <> show a' <> ")"
    Left a' -> absurd a'

instance (Typeable t, Show t, Show (Poly (t1 : tn))) => Show (Poly (t : t1 : tn)) where
  show a = case polycast @t a of
    Right a' -> "Poly (" <> show (typeOf a') <> "; " <> show a' <> ")"
    Left a' -> show a'

-- Eq instances

instance (Typeable t, Eq t) => Eq (Poly '[t]) where
  a == b = polycast @t a == polycast @t b

instance (Typeable t, Eq t, Eq (Poly (t1 : tn))) => Eq (Poly (t : t1 : tn)) where
  a == b = case (polycast @t a, polycast @t b) of
    (Right a', Right b') -> a' == b'
    (Left a', Left b') -> a' == b'
    _ -> False

-- Ord instance

instance (Typeable t, Ord t) => Ord (Poly '[t]) where
  compare a b = compare (polycast @t a) (polycast @t b)

-- | Since there's no way to compare two values of different types,
-- those pairs will be compared by the order of types in the list.
--
-- This means that the order of types in the list matters and ordering
-- should be stable and determined by the actual type list,
-- compared to the alternative that is ordering based on the `TypeRep`,
-- which could be unstable and depend on the compiler.
--
-- TODO: Test
instance (Typeable t, Ord t, Ord (Poly (t1 : tn))) => Ord (Poly (t : t1 : tn)) where
  compare a b = case (polycast @t a, polycast @t b) of
    (Right a', Right b') -> compare a' b'
    (Left a', Left b') -> compare a' b'
    -- 'a' is of type 't', but 'b' is one of type 't1 : tn', so 'b' is further down the
    -- type list and thus `a < b`.
    (Right _, Left _) -> LT
    -- Same as above, but reversed.
    (Left _, Right _) -> GT
