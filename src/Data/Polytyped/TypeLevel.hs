{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Polytyped.TypeLevel where

import Data.Kind
import Data.Type.Bool
import GHC.TypeError

-- | Requires that the type @t@ is one of the types in the list @ts@.
type OneOf a (ts :: [Type]) =
  If
    (IsElem a ts)
    (() :: Constraint)
    ( TypeError
        ( 'Text "Constraint 'OneOf " :<>: 'ShowType a :<>: 'Text " (" :<>: 'ShowType ts :<>: 'Text ")' could not be satisfied."
            :$$: 'Text "Type " :<>: 'ShowType a :<>: 'Text " is not one of the supported types: " :<>: 'ShowType ts
        )
    )

-- | Checks if the type @t@ is present in the list @ts@.
type family IsElem (t :: Type) (ts :: [Type]) :: Bool where
  IsElem t '[] = 'False
  IsElem t (t : ts) = 'True
  IsElem t (t1 : ts) = IsElem t ts

-- | Checks if the type list @sub@ is subset of the type list @super@.
type family IsSubsetOf (sub :: [Type]) (super :: [Type]) :: Bool where
  IsSubsetOf '[] _ = 'True
  IsSubsetOf (s : ss) ts = IsElem s ts && IsSubsetOf ss ts

-- | Requires that the type list @sub@ is subset of the type list @super@.
type family SubsetOf (sub :: [Type]) (super :: [Type]) :: Constraint where
  SubsetOf sub super =
    If
      (IsSubsetOf sub super)
      (() :: Constraint)
      ( TypeError
          ( 'Text "Constraint 'SubsetOf (" :<>: 'ShowType sub :<>: 'Text ") (" :<>: 'ShowType super :<>: 'Text ")' could not be satisfied."
              :$$: 'ShowType sub :<>: 'Text " is not a subset of " :<>: 'ShowType super
          )
      )

-- | Checks if the types in the list are unique.
type family IsUnique (ts :: [Type]) :: Bool where
  IsUnique '[] = 'True
  IsUnique (t : ts) = (Not (IsElem t ts)) && IsUnique ts

-- | Requires that the types in the list are unique.
type family Unique (ts :: [Type]) :: Constraint where
  Unique ts =
    If
      (IsUnique ts)
      (() :: Constraint)
      ( TypeError
          ( 'Text "Constraint 'Unique (" :<>: 'ShowType ts :<>: 'Text ")' could not be satisfied."
              :$$: 'Text "Types in the list are not unique: " :<>: 'ShowType ts
          )
      )

-- | Drops the first occurrence of the type from the list.
-- The type must be present in the list.
type DropElem (t :: Type) (ts :: [Type]) =
  If
    (IsElem t ts)
    (DropElem' t ts)
    ( TypeError
        ( 'Text "Can't 'DropElem (" :<>: 'ShowType t :<>: 'Text ") (" :<>: 'ShowType ts :<>: 'Text ")'"
            :$$: 'Text "Type is not present in the list: " :<>: 'ShowType ts
        )
    )

-- | Just like `DropElem`, but without the check for the type presence.
-- If the type is not present in the list, it will act as identity.
type family DropElem' (t :: Type) (ts :: [Type]) :: [Type] where
  DropElem' t '[] = '[]
  DropElem' t (t : ts) = ts
  DropElem' t (t1 : ts) = t1 : DropElem t ts

-- | Replaces the first occurrence of the type in the list with another type.
-- The replaced type must be present in the list, the new type can't.
type ReplaceElem (t :: Type) (u :: Type) (ts :: [Type]) =
  If
    (IsElem t ts)
    ( If
        (IsElem u ts)
        ( TypeError
            ( 'Text "Can't (ReplaceElem " :<>: 'ShowType t :<>: 'Text " " :<>: 'ShowType u :<>: 'Text ")"
                :$$: 'Text "Type '" :<>: 'ShowType u :<>: 'Text "' is already present in the list: " :<>: 'ShowType ts
            )
        )
        (ReplaceElem' t u ts)
    )
    ( TypeError
        ( 'Text "Can't (ReplaceElem " :<>: 'ShowType t :<>: 'Text " " :<>: 'ShowType u :<>: 'Text ")"
            :$$: 'Text "Type '" :<>: 'ShowType t :<>: 'Text "' is not present in the list: " :<>: 'ShowType ts
        )
    )

-- | Just like `ReplaceElem`, but without the check for the type presence.
type family ReplaceElem' (t :: Type) (u :: Type) (ts :: [Type]) :: [Type] where
  ReplaceElem' t u '[] = '[]
  ReplaceElem' t u (t : ts) = u : ts
  ReplaceElem' t u (t1 : ts) = t1 : ReplaceElem' t u ts
