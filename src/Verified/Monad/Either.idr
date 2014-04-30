module Verified.Monad.Either

import Verified.Monad
import Verified.Applicative.Either

instance VerifiedMonad (Either e) where
  monadLeftIdentity _ _ = refl
  monadRightIdentity (Left _) = refl
  monadRightIdentity (Right _) = refl
  monadAssociativity (Left _) f g = refl
  monadAssociativity (Right _) f g = refl
