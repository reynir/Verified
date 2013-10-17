module Verified.Functor.Either

import Verified.Functor

instance VerifiedFunctor (Either e) where
  functorIdentity (Left _) = refl
  functorIdentity (Right _) = refl
  functorComposition (Left _) g1 g2 = refl
  functorComposition (Right _) g1 g2 = refl
