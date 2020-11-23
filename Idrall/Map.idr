module Idrall.Map

-- helper functions for Map and SortedMap

import Idrall.Expr
import Idrall.Error
import Idrall.Value

import Data.List

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

-- Errors on collision
export
mergeWith : Show k => Eq k => Ord k =>
            (Value -> Value -> Either Error Value) ->
            SortedMap k Value ->
            SortedMap k Value ->
            Either Error (SortedMap k Value)
mergeWith f x y =
  let xs = Data.SortedMap.toList x
      ys = Data.SortedMap.toList y in
  Right $ fromList !(combineLists xs ys)
where
  replaceWith : (k, Value) -> List (k, Value) -> List (k, Value)
  replaceWith (k, v) xs =
    let rem = filter (\(k',_) => not (k == k')) xs in
    (k, v) :: rem

  combineLists : List (k, Value) -> List (k, Value) -> Either Error (List (k, Value))
  combineLists xs [] = Right xs
  combineLists [] ys = Right ys
  combineLists xs ((k, y) :: ys) = do
    rest <- combineLists xs ys
    case lookup k rest of
         Nothing => Right $ (k, y) :: rest
         (Just x) =>
            case (x, y) of
                 (VRecord x', VRecord y') => let nested = !(f x y)
                                                 newKv = (k, nested)
                                                 res = replaceWith newKv rest in
                                                 pure res
                 (VRecordLit x', VRecordLit y') => let nested = !(f x y)
                                                       newKv = (k, nested)
                                                       res = replaceWith newKv rest in
                                                       pure res
                 (w, q) => Left $ RecordFieldCollision (show k ++ " when combining " ++ (show w) ++ "<>" ++ (show q))
