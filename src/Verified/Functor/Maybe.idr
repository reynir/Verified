module Verified.Functor.Maybe

import Verified.Functor

instance VerifiedFunctor Maybe where
  mapPreservesIdentity Nothing = refl
  mapPreservesIdentity (Just x) = refl
  mapComposition Nothing g1 g2 = refl
  mapComposition (Just x) g1 g2 = refl
