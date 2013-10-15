module Verified.Functor.List

import Verified.Functor

instance VerifiedFunctor List where
  mapPreservesIdentity [] = refl
  mapPreservesIdentity (x :: xs) = 
    let Hxs = mapPreservesIdentity xs in ?lemma
