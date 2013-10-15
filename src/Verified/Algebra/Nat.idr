module Verified.Algebra.Nat

fromAdditive : Additive -> Nat
fromAdditive (getAdditive n) = n

natAndAdditive1 : fromAdditive (getAdditive n) = n
natAndAdditive1 = refl

natAndAdditive2 : getAdditive (fromAdditive n) = n
natAndAdditive2 {n=getAdditive n'}= refl

natAndAdditiveOp1 : fromAdditive (getAdditive n <+> getAdditive m) = n + m
natAndAdditiveOp1 = refl

natAndAdditiveOp2 : getAdditive (fromAdditive n + fromAdditive m) = n <+> m
natAndAdditiveOp2 {n=getAdditive n'} {m=getAdditive m'} = refl

fromMultiplicative : Multiplicative -> Nat
fromMultiplicative (getMultiplicative n) = n

natAndMultiplicative1 : fromMultiplicative (getMultiplicative n) = n
natAndMultiplicative1 = refl

natAndMultiplicative2 : getMultiplicative (fromMultiplicative n) = n
natAndMultiplicative2 {n=getMultiplicative n'} = refl

natAndMultiplicativeOp1 : fromMultiplicative (getMultiplicative n <+> getMultiplicative m) = n * m
natAndMultiplicativeOp1 = refl

natAndMultiplicativeOp2 : getMultiplicative (fromMultiplicative n * fromMultiplicative m) = n <+> m
natAndMultiplicativeOp2 {n=getMultiplicative n'} {m=getMultiplicative m'} = refl

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

Verified.Algebra.Nat.lemmaMultiplicativeNeutralL = proof
  intros
  rewrite multOneRightNeutral l
  exact refl 


Verified.Algebra.Nat.lemmaMultiplicativeNeutralR = proof
  intros
  rewrite multOneLeftNeutral r
  exact refl 


Verified.Algebra.Nat.lemmaMultiplicativeAssoc = proof
  intros
  rewrite multAssociative l c r
  exact refl


Verified.Algebra.Nat.lemmaAdditiveNeutralL = proof
  intros
  rewrite (plusZeroRightNeutral l)
  exact refl


Verified.Algebra.Nat.lemmaAdditiveNeutralR = proof
  intros
  exact refl


Verified.Algebra.Nat.lemmaAdditiveAssoc = proof
  intros
  rewrite (plusAssociative l c r)
  exact refl


