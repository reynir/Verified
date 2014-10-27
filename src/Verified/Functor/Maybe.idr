module Verified.Functor.Maybe

import Verified.Functor

instance VerifiedFunctor Maybe where
  functorIdentity Nothing = Refl
  functorIdentity (Just x) = Refl
  functorComposition Nothing g1 g2 = Refl
  functorComposition (Just x) g1 g2 = Refl
