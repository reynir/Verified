module Verified.Algebra.Bool

import Prelude.Algebra

%default total

instance Semigroup Bool where
  (<+>) = (||)

instance VerifiedSemigroup Bool where
  semigroupOpIsAssociative True _ _ = refl
  semigroupOpIsAssociative False True _ = refl
  semigroupOpIsAssociative False False True = refl
  semigroupOpIsAssociative False False False = refl

instance Monoid Bool where
  neutral = False

instance VerifiedMonoid Bool where
  monoidNeutralIsNeutralL True = refl
  monoidNeutralIsNeutralL False = refl
  monoidNeutralIsNeutralR r = refl
