module Verified.Algebra.Bool

import Prelude.Algebra

%default total

instance Semigroup Bool where
  (<+>) = (||)

instance VerifiedSemigroup Bool where
  semigroupOpIsAssociative True _ _ = Refl
  semigroupOpIsAssociative False True _ = Refl
  semigroupOpIsAssociative False False True = Refl
  semigroupOpIsAssociative False False False = Refl

instance Monoid Bool where
  neutral = False

instance VerifiedMonoid Bool where
  monoidNeutralIsNeutralL True = Refl
  monoidNeutralIsNeutralL False = Refl
  monoidNeutralIsNeutralR r = Refl
