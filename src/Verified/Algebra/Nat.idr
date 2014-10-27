module Verified.Algebra.Nat

%default total

fromAdditive : Additive -> Nat
fromAdditive (getAdditive n) = n

natAndAdditive1 : fromAdditive (getAdditive n) = n
natAndAdditive1 = Refl

natAndAdditive2 : getAdditive (fromAdditive n) = n
natAndAdditive2 {n=getAdditive n'}= Refl

natAndAdditiveOp1 : fromAdditive (getAdditive n <+> getAdditive m) = n + m
natAndAdditiveOp1 = Refl

natAndAdditiveOp2 : getAdditive (fromAdditive n + fromAdditive m) = n <+> m
natAndAdditiveOp2 {n=getAdditive n'} {m=getAdditive m'} = Refl

fromMultiplicative : Multiplicative -> Nat
fromMultiplicative (getMultiplicative n) = n

natAndMultiplicative1 : fromMultiplicative (getMultiplicative n) = n
natAndMultiplicative1 = Refl

natAndMultiplicative2 : getMultiplicative (fromMultiplicative n) = n
natAndMultiplicative2 {n=getMultiplicative n'} = Refl

natAndMultiplicativeOp1 : fromMultiplicative (getMultiplicative n <+> getMultiplicative m) = n * m
natAndMultiplicativeOp1 = Refl

natAndMultiplicativeOp2 : getMultiplicative (fromMultiplicative n * fromMultiplicative m) = n <+> m
natAndMultiplicativeOp2 {n=getMultiplicative n'} {m=getMultiplicative m'} = Refl

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
  exact Refl 


Verified.Algebra.Nat.lemmaMultiplicativeNeutralR = proof
  intros
  rewrite multOneLeftNeutral r
  exact Refl 


Verified.Algebra.Nat.lemmaMultiplicativeAssoc = proof
  intros
  rewrite multAssociative l c r
  exact Refl


Verified.Algebra.Nat.lemmaAdditiveNeutralL = proof
  intros
  rewrite (plusZeroRightNeutral l)
  exact Refl


Verified.Algebra.Nat.lemmaAdditiveNeutralR = proof
  intros
  exact Refl


Verified.Algebra.Nat.lemmaAdditiveAssoc = proof
  intros
  rewrite (plusAssociative l c r)
  exact Refl


