module Verified.Functor.Vect

import Data.Vect
import Verified.Functor

instance VerifiedFunctor (Vect n) where
  functorIdentity [] = Refl
  functorIdentity (x :: xs) =
    let IHxs = functorIdentity xs in ?lemma1
  functorComposition [] g1 g2 = Refl
  functorComposition (x :: xs) g1 g2 =
    let IHxs = functorComposition xs g1 g2 in ?lemma2

---------- Proofs ----------

Verified.Functor.Vect.lemma2 = proof
  intros
  rewrite IHxs 
  exact Refl


Verified.Functor.Vect.lemma1 = proof
  intros
  rewrite IHxs 
  exact Refl
