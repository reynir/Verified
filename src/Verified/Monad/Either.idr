module Verified.Monad.Either

import Verified.Monad
import Verified.Applicative.Either

instance VerifiedMonad (Either e) where
  monadLeftIdentity _ _ = Refl
  monadRightIdentity (Left _) = Refl
  monadRightIdentity (Right _) = Refl
  monadAssociativity (Left _) f g = Refl
  monadAssociativity (Right _) f g = Refl
