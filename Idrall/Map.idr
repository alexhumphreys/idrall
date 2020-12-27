module Idrall.Map

-- helper functions for Map and SortedMap

import Idrall.Expr
import Idrall.Error
import Idrall.Value

import Data.List

export
isOdd : Nat -> Bool
isOdd Z = False
isOdd (S k) = not (isOdd k)

export
isEven : Nat -> Bool
isEven k = not $ isOdd k

export
mapChunks : (a -> Either e b) -> (k, a) -> Either e (k, b)
mapChunks f (k, a) = Right (k, !(f a))

export
mapListEither : List a -> (a -> Either e b) -> Either e (List b)
mapListEither [] f = Right []
mapListEither (x :: xs) f =
  do rest <- mapListEither xs f
     x' <- f x
     Right (x' :: rest)

export
mapRecord : (a -> Either e b) -> (k, a) -> Either e (k, b)
mapRecord f (k, x) = Right (k, !(f x))

export
mapUnion : (a -> Either e b) -> (k, Maybe a) -> Either e (k, (Maybe b))
mapUnion f (k, Just x) =
  Right (k, Just !(f x))
mapUnion f (k, Nothing) = Right (k, Nothing)

export
mapMaybe : (a -> Either e b) -> Maybe a -> Either e (Maybe b)
mapMaybe f (Just x) =
  Right $ Just !(f x)
mapMaybe f Nothing = Right Nothing

export
mergeWithApp : (Monad m, Ord k) =>
               (a -> a -> m a) ->
               SortedMap k a ->
               SortedMap k a ->
               m (SortedMap k a)
mergeWithApp f xs ys = sequence (mergeWith (\x,y => (f <$> x <*> y) >>= id) (map pure xs) (map pure ys))

export
mergeWithApp' : (Monad m, Ord k) =>
               (a -> a -> m a) ->
               SortedMap k a ->
               SortedMap k a ->
               m (SortedMap k a)
mergeWithApp' f xs ys = sequence (mergeWith (\x,y => y) (map pure xs) (map pure ys))

replace : Eq a => (needle : List a) -> (replacement : List a) -> (haystack : List a) -> List a
replace needle replacement haystack = go 0 [] needle haystack
  where
    go : (pass : Nat) ->
         (acc : List a) ->
         (needle : List a) ->
         (haystack : List a) -> List a
    go _ acc (x :: xs) [] = acc -- End of list
    go _ acc [] haystack = haystack -- Empty needle
    go (S k) acc needle (y :: haystack) = -- Pass through to remove matched elements
      go k acc needle haystack
    go Z acc needle@(x :: xs) h@(y :: haystack) =
      case isPrefixOf needle h of
           False => go 0 (acc ++ [y]) needle haystack
           True => go (length xs) (acc ++ replacement) needle haystack

export
textReplace : (needle : String) -> (replacement : String) -> (haystack : String) -> String
textReplace needle replacement haystack = pack $ replace (unpack needle) (unpack replacement) (unpack haystack)
