module Verified.Applicative

import Verified.Functor

%default total

class (Applicative f, VerifiedFunctor f) => VerifiedApplicative (f : Type -> Type) where
  applicativeMap : (x : f a) -> (g : a -> b) ->
                   map g x = pure g <$> x
  applicativeIdentity : (x : f a) -> pure id <$> x = x
  applicativeComposition : (x : f a) -> (g1 : f (a -> b)) -> (g2 : f (b -> c)) ->
                           ((pure (.) <$> g2) <$> g1) <$> x = g2 <$> (g1 <$> x)
  applicativeHomomorphism : (x : a) -> (g : a -> b) ->
                            (<$>) {f} (pure g) (pure x) = pure {f} (g x)
  applicativeInterchange : (x : a) -> (g : f (a -> b)) ->
                           g <$> pure x = pure (\g' : a -> b => g' x) <$> g
