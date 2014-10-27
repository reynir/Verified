module Verified.Applicative.Maybe

import Verified.Applicative
import Verified.Functor.Maybe

instance VerifiedApplicative Maybe where
  applicativeMap Nothing g = Refl
  applicativeMap (Just x) g = Refl
  applicativeIdentity Nothing = Refl
  applicativeIdentity (Just x) = Refl
  applicativeComposition Nothing g1 g2 = Refl
  applicativeComposition (Just x) Nothing g2 = Refl
  applicativeComposition (Just x) (Just g1) Nothing = Refl
  applicativeComposition (Just x) (Just g1) (Just g2) = Refl
  applicativeHomomorphism x g = Refl
  applicativeInterchange x Nothing = Refl
  applicativeInterchange x (Just g) = Refl
