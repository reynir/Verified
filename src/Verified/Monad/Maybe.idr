module Verified.Monad.Maybe

import Verified.Monad
import Verified.Applicative.Maybe

instance VerifiedMonad Maybe where
  monadLeftIdentity x f = refl
  monadRightIdentity (Just x) = refl
  monadRightIdentity Nothing = refl
  monadAssociativity Nothing f g = refl
  monadAssociativity (Just x) f g = refl
