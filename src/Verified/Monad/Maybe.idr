module Verified.Monad.Maybe

import Verified.Applicative
import Verified.Monad
import Verified.Applicative.Maybe

instance VerifiedMonad Maybe where
  monadApplicative Nothing Nothing = Refl
  monadApplicative Nothing (Just x) = Refl
  monadApplicative (Just f) Nothing = Refl
  monadApplicative (Just f) (Just x) = Refl
  monadLeftIdentity x f = Refl
  monadRightIdentity (Just x) = Refl
  monadRightIdentity Nothing = Refl
  monadAssociativity Nothing f g = Refl
  monadAssociativity (Just x) f g = Refl
