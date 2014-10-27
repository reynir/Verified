module Verified.Applicative.Either

import Verified.Applicative
import Verified.Functor.Either

instance VerifiedApplicative (Either a) where
  applicativeMap (Left _) _ = Refl
  applicativeMap (Right _) _ = Refl
  applicativeIdentity (Left _) = Refl
  applicativeIdentity (Right _) = Refl
  applicativeComposition x g1 (Left _) = Refl
  applicativeComposition x (Left _) (Right _) = Refl
  applicativeComposition (Left x) (Right _) (Right _) = Refl
  applicativeComposition (Right _) (Right _) (Right _) = Refl
  applicativeHomomorphism x g = Refl
  applicativeInterchange x (Left _) = Refl
  applicativeInterchange x (Right _) = Refl
