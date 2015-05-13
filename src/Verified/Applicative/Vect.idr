module Verified.Applicative.Vect

import Data.Vect
import Verified.Applicative
import Verified.Functor
import Verified.Functor.Vect


applicativeMap_Vect : (vs : Vect n a) -> (g : a -> b) -> map g vs = pure g <*> vs
applicativeMap_Vect []        g = Refl
applicativeMap_Vect (v :: vs) g = rewrite (applicativeMap_Vect vs g) in Refl


applicativeIdentity_Vect : (vs : Vect n a) -> pure id <*> vs = vs
applicativeIdentity_Vect []        = Refl
applicativeIdentity_Vect (x :: xs) = rewrite (applicativeIdentity_Vect xs) in Refl


applicativeInterchange_Vect : (x : a) -> (g : Vect n (a -> b)) -> g <*> pure x = pure (\g' => g' x) <*> g
applicativeInterchange_Vect x []        = Refl
applicativeInterchange_Vect x (f :: fs) = rewrite (applicativeInterchange_Vect x fs) in Refl


applicativeComposition_Vect : (xs : Vect n a) -> (g1 : Vect n (a -> b)) -> (g2 : Vect n (b -> c))
                           -> pure (.) <*> g2 <*> g1 <*> xs = g2 <*> (g1 <*> xs)
applicativeComposition_Vect []        []          []          = Refl
applicativeComposition_Vect (v :: vs) (g1 :: g1s) (g2 :: g2s) = rewrite (applicativeComposition_Vect vs g1s g2s) in Refl


applicativeHomomorphism_Vect : {n : Nat} -> (x : a) -> (g : a -> b)
                            -- pure g <*> pure x = pure (g x)
                            -> Vect.zipWith apply (Vect.replicate n g) (Vect.replicate n x) = Vect.replicate n (g x)
applicativeHomomorphism_Vect {n =    Z } x g = Refl
applicativeHomomorphism_Vect {n = (S k)} x g = rewrite (applicativeHomomorphism_Vect x g {n=k}) in Refl


instance VerifiedApplicative (Vect vlen) where
  applicativeMap = applicativeMap_Vect
  applicativeIdentity = applicativeIdentity_Vect
  applicativeInterchange = applicativeInterchange_Vect
  applicativeComposition = applicativeComposition_Vect
  applicativeHomomorphism = applicativeHomomorphism_Vect

