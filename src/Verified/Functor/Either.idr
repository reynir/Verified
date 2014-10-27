module Verified.Functor.Either

import Verified.Functor

instance VerifiedFunctor (Either e) where
  functorIdentity (Left _) = Refl
  functorIdentity (Right _) = Refl
  functorComposition (Left _) g1 g2 = Refl
  functorComposition (Right _) g1 g2 = Refl
