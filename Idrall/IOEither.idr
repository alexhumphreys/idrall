module Idrall.IOEither

public export
data IOEither a b
 = MkIOEither (IO (Either a b))

export
Functor (IOEither a) where
  map func (MkIOEither x) = MkIOEither (map (map func) x)

||| Lift a two-argument function to an applicative
export
liftA2 : Applicative f => (a -> b -> c) -> f a -> f b -> f c
liftA2 f a b = (map f a) <*> b

export
Applicative (IOEither a) where
  pure x = MkIOEither (pure (pure x))
  (<*>) (MkIOEither x) (MkIOEither y) = MkIOEither (liftA2 (<*>) x y)

export
Monad (IOEither a) where
  (>>=) (MkIOEither x) f = MkIOEither (do x' <- x
                                          (case x' of
                                                (Left l) => pure (Left l)
                                                (Right r) => let MkIOEither g = f r in
                                                                 g))
  join x = x >>= id

export
liftEither : Either e a -> IOEither e a
liftEither = MkIOEither . pure

export
liftIOEither : IOEither e a -> IO (Either e a)
liftIOEither (MkIOEither x) = x

export
mapErr : (e -> e') -> IOEither e a -> IOEither e' a
mapErr f (MkIOEither x) = MkIOEither (do
  x' <- x
  case x' of
        (Left l) => pure (Left (f l))
        (Right r) => pure (Right r))

