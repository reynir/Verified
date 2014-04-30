module Verified.Applicative.Either

import Verified.Applicative

instance VerifiedApplicative (Either a) where
  applicativeMap (Left _) _ = refl
  applicativeMap (Right _) _ = refl
  applicativeIdentity (Left _) = refl
  applicativeIdentity (Right _) = refl
  applicativeComposition x g1 (Left _) = refl
  applicativeComposition x (Left _) (Right _) = refl
  applicativeComposition (Left x) (Right _) (Right _) = refl
  applicativeComposition (Right _) (Right _) (Right _) = refl
  applicativeHomomorphism x g = refl
  applicativeInterchange x (Left _) = refl
  applicativeInterchange x (Right _) = refl
