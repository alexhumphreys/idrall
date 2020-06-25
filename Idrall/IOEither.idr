module Idrall.IOEither

public export
data IOEither a b
 = MkIOEither (IO (Either a b))

export
Functor (IOEither a) where
  map func (MkIOEither x) = MkIOEither (map (map func) x)

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
