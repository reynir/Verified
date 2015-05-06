module Verified.Algebra.Bool

import Classes.Verified
import Prelude.Algebra

%default total

instance Semigroup Bool where
  -- Laziness intereferes with the types
  (<+>) = \b1, b2 => b1 || b2

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
