module Verified.Applicative.Maybe

import Verified.Applicative
import Verified.Functor.Maybe

instance VerifiedApplicative Maybe where
  applicativeMap Nothing g = refl
  applicativeMap (Just x) g = refl
  applicativeIdentity Nothing = refl
  applicativeIdentity (Just x) = refl
  applicativeComposition Nothing g1 g2 = refl
  applicativeComposition (Just x) Nothing g2 = refl
  applicativeComposition (Just x) (Just g1) Nothing = refl
  applicativeComposition (Just x) (Just g1) (Just g2) = refl
  applicativeHomomorphism x g = refl
  applicativeInterchange x Nothing = refl
  applicativeInterchange x (Just g) = refl
