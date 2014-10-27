module Verified.Monad.Maybe

import Verified.Monad
import Verified.Applicative.Maybe

instance VerifiedMonad Maybe where
  monadLeftIdentity x f = Refl
  monadRightIdentity (Just x) = Refl
  monadRightIdentity Nothing = Refl
  monadAssociativity Nothing f g = Refl
  monadAssociativity (Just x) f g = Refl
