module Verified.Functor.Maybe

import Verified.Functor

instance VerifiedFunctor Maybe where
  functorIdentity Nothing = refl
  functorIdentity (Just x) = refl
  functorComposition Nothing g1 g2 = refl
  functorComposition (Just x) g1 g2 = refl
