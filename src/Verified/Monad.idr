module Verified.Monad

import Verified.Applicative

%default total

class (Monad m, VerifiedApplicative m) => VerifiedMonad (m : Type -> Type) where
  monadApplicative : (mf : m (a -> b)) -> (mx : m a) ->
                     mf <*> mx = mf >>= \f =>
                                 mx >>= \x =>
                                        pure (f x)
  monadLeftIdentity : (x : a) -> (f : a -> m b) -> return x >>= f = f x
  monadRightIdentity : (mx : m a) -> mx >>= return = mx
  monadAssociativity : (mx : m a) -> (f : a -> m b) -> (g : b -> m c) -> 
                       (mx >>= f) >>= g = mx >>= (\x => f x >>= g)
