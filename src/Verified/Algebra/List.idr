module Verified.Algebra.List

%default total

instance VerifiedSemigroup (List a) where
  semigroupOpIsAssociative = appendAssociative

instance VerifiedMonoid (List a) where
  monoidNeutralIsNeutralL = appendNilRightNeutral
  monoidNeutralIsNeutralR xs = Refl
