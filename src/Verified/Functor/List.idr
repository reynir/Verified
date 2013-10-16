module Verified.Functor.List

import Verified.Functor

instance VerifiedFunctor List where
  functorIdentity [] = refl
  functorIdentity (x :: xs) = 
    let IHxs = functorIdentity xs in ?lemma1
  functorComposition [] g1 g2 = refl
  functorComposition (x :: xs) g1 g2 =
    let IHxs = functorComposition xs g1 g2 in ?lemma2

---------- Proofs ----------

Verified.Functor.List.lemma2 = proof
  intros
  rewrite IHxs 
  exact refl


Verified.Functor.List.lemma1 = proof
  intros
  rewrite IHxs 
  exact refl


