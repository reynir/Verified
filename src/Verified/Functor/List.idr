module Verified.Functor.List

import Verified.Functor

instance VerifiedFunctor List where
  mapPreservesIdentity [] = refl
  mapPreservesIdentity (x :: xs) = 
    let IHxs = mapPreservesIdentity xs in ?lemma1
  mapComposition [] g1 g2 = refl
  mapComposition (x :: xs) g1 g2 =
    let IHxs = mapComposition xs g1 g2 in ?lemma2
