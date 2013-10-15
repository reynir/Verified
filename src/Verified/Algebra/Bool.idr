module Verified.Algebra.Bool

import Prelude.Algebra

instance Semigroup Bool where
  (<+>) = (||)

instance VerifiedSemigroup Bool where
  semigroupOpIsAssociative True True r = refl
  semigroupOpIsAssociative True False True = refl
  semigroupOpIsAssociative True False False = refl
  semigroupOpIsAssociative False c r = refl

instance Monoid Bool where
  neutral = False

instance VerifiedMonoid Bool where
  monoidNeutralIsNeutralL True = refl
  monoidNeutralIsNeutralL False = refl
  monoidNeutralIsNeutralR r = refl
