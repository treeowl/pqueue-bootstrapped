module Loop2 where

import qualified Prio2 as P
import Data.Coerce
import qualified Data.Foldable as Foldable
import Prelude hiding (null)

-- | A priority queue holding keys of type @k@, /strict/ values of type @Loop2
-- k a@, and /lazy/ values of type @a@. This is kind of weird by itself, but
-- implementing priority queue operations for it lets us implement bootstrapped
-- queues (arguably) more cleanly.
newtype Loop2 k a = Loop2 { unLoop2 :: P.MinPQueue2 k (Loop2 k a) a }

empty :: Loop2 k a
empty = Loop2 P.empty

null :: Loop2 k a -> Bool
null (Loop2 q) = P.null q

size :: Loop2 k a -> Int
size (Loop2 q) = P.size q

insert :: Ord k => k -> a -> Loop2 k a -> Loop2 k a -> Loop2 k a
insert k a l (Loop2 q) = Loop2 (P.insert k a l q)

insertEager :: Ord k => k -> a -> Loop2 k a -> Loop2 k a -> Loop2 k a
insertEager k a l (Loop2 q) = Loop2 (P.insertEager k a l q)

minViewWithKey :: Ord k => Loop2 k a -> Maybe ((k, a, Loop2 k a), Loop2 k a)
minViewWithKey (Loop2 q) = coerce $ P.minViewWithKey q

merge :: Ord k => Loop2 k a -> Loop2 k a -> Loop2 k a
merge (Loop2 p) (Loop2 q) = Loop2 (P.merge p q)

-- | Convert a list of keys and lazy values to a 'Loop2', pairing each key with
-- an empty 'Loop2'.  Return the 'Loop2' and its size.
fromKVList :: Ord k => [(k, a)] -> (Int, Loop2 k a)
-- We calculate the size at the end rather than tracking it along the way; I'm
-- not sure which approach is better, but this way is simpler and should
-- be cheap enough, at least for non-tiny queues.
fromKVList xs =
  let
    !q = Foldable.foldl' (\acc (k, a) -> insertEager k a empty acc) empty xs
    !s = size q
  in (s, q)

mapWithKey :: forall k a b. (k -> a -> b) -> Loop2 k a -> Loop2 k b
mapWithKey f = go
  where
    go :: Loop2 k a -> Loop2 k b
    go (Loop2 q) = Loop2 $ P.wonkyMap f go q
