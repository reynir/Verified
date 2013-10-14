module Prelude.VerifiedAlgebra.Nat

instance VerifiedSemigroup Additive where
  semigroupOpIsAssociative (getAdditive l) (getAdditive c) (getAdditive r) =
    ?lemmaAdditiveAssoc

instance VerifiedMonoid Additive where
  monoidNeutralIsNeutralL (getAdditive l) = ?lemmaAdditiveNeutralL
  monoidNeutralIsNeutralR (getAdditive r) = ?lemmaAdditiveNeutralR

instance VerifiedSemigroup Multiplicative where
  semigroupOpIsAssociative (getMultiplicative l) (getMultiplicative c) (getMultiplicative r) =
    ?lemmaMultiplicativeAssoc

instance VerifiedMonoid Multiplicative where
  monoidNeutralIsNeutralL (getMultiplicative l) = ?lemmaMultiplicativeNeutralL
  monoidNeutralIsNeutralR (getMultiplicative r) = ?lemmaMultiplicativeNeutralR

---------- Proofs ----------

Prelude.VerifiedAlgebra.Nat.lemmaMultiplicativeNeutralL = proof
  intros
  rewrite multOneRightNeutral l
  exact refl 


Prelude.VerifiedAlgebra.Nat.lemmaMultiplicativeNeutralR = proof
  intros
  rewrite multOneLeftNeutral r
  exact refl 


Prelude.VerifiedAlgebra.Nat.lemmaMultiplicativeAssoc = proof
  intros
  rewrite multAssociative l c r
  exact refl


Prelude.VerifiedAlgebra.Nat.lemmaAdditiveNeutralL = proof
  intros
  rewrite (plusZeroRightNeutral l)
  exact refl


Prelude.VerifiedAlgebra.Nat.lemmaAdditiveNeutralR = proof
  intros
  exact refl


Prelude.VerifiedAlgebra.Nat.lemmaAdditiveAssoc = proof
  intros
  rewrite (plusAssociative l c r)
  exact refl


