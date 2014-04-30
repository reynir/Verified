module Verified.Functor

%default total

class Functor f => VerifiedFunctor (f : Type -> Type) where
  functorIdentity : {a : Type} -> (x : f a) -> map id x = id x
  functorComposition : {a : Type} -> {b : Type} -> (x : f a) ->
                   (g1 : a -> b) -> (g2 : b -> c) ->
                   map (g2 . g1) x = (map g2 . map g1) x
