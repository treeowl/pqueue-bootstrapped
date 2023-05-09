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

mapWithKey' :: forall k a b. (k -> a -> b) -> Loop2 k a -> Loop2 k b
mapWithKey' f = go
  where
    go :: Loop2 k a -> Loop2 k b
    go (Loop2 q) = Loop2 $ P.wonkyMap' f go q

mapWithKey# :: forall k a b. (k -> a -> (# b #)) -> Loop2 k a -> Loop2 k b
mapWithKey# f = go
  where
    go :: Loop2 k a -> Loop2 k b
    go (Loop2 q) = Loop2 $ P.wonkyMap# f go q

traverseWithKeyU :: forall f k a b. Applicative f => (k -> a -> f b) -> Loop2 k a -> f (Loop2 k b)
traverseWithKeyU f = go
  where
    go :: Loop2 k a -> f (Loop2 k b)
    go (Loop2 q) = P.wonkTrav Loop2 f go q

foldMapWithKeyU :: forall k a m. Monoid m => (k -> a -> m) -> Loop2 k a -> m
foldMapWithKeyU f = go
  where
    go :: Loop2 k a -> m
    go (Loop2 q) = P.wonkFoldMap f go q

-- | Convert an ascending list of keys to a 'Loop2', pairing each with an empty 'Loop2'.
-- Return the 'Loop2' and its size, along with the minimum entry.
fromAscKVList :: [(k,a)] -> Maybe (Int, k, a, Loop2 k a)
-- We calculate the size at the end rather than tracking it along the way; I'm
-- not sure which approach is better, but this way is simpler and should
-- be cheap enough, at least for non-tiny queues.
fromAscKVList xs = case Foldable.foldl' go NoFkl xs of
  NoFkl -> Nothing
  Fkl the_min min_val q ->
    let !s = size q + 1
    in Just (s, the_min, min_val, q)
  where
    go NoFkl (k, a) = Fkl k a empty
    go (Fkl mini miniv l) (k, a) = Fkl mini miniv (insertMaxQEager k a empty l)
-- TODO: We actually want to get list fusion. Currently, that's not
-- happening. Let's figure out how to fix that.
{-# INLINE fromAscKVList #-}

insertMaxQ :: k -> a -> Loop2 k a -> Loop2 k a -> Loop2 k a
insertMaxQ k a v (Loop2 q) = Loop2 (P.insertMaxQ k a v q)

insertMinQ :: k -> a -> Loop2 k a -> Loop2 k a -> Loop2 k a
insertMinQ k a v (Loop2 q) = Loop2 (P.insertMinQ k a v q)

insertMaxQEager :: k -> a -> Loop2 k a -> Loop2 k a -> Loop2 k a
insertMaxQEager k a v (Loop2 q) = Loop2 (P.insertMaxQEager k a v q)

insertMinQEager :: k -> a -> Loop2 k a -> Loop2 k a -> Loop2 k a
insertMinQEager k a v (Loop2 q) = Loop2 (P.insertMinQEager k a v q)

data Fkl k a = NoFkl | Fkl !k a !(Loop2 k a)

-- | Convert a descending list of keys to a 'Loop', pairing each with an empty 'Loop'.
-- Return the 'Loop' and its size, along with the minimum element.
fromDescKVList :: [(k, a)] -> Maybe (Int, k, a, Loop2 k a)
-- We calculate the size at the end rather than tracking it along the way; I'm
-- not sure which approach is better, but this way is simpler and should
-- be cheap enough, at least for non-tiny queues.
fromDescKVList xs = case Foldable.foldl' go NoFkl xs of
  NoFkl -> Nothing
  Fkl the_min min_val q ->
    let !s = size q + 1
    in Just (s, the_min, min_val, q)
  where
    go NoFkl (k, a) = Fkl k a empty
    go (Fkl mini miniv l) (k, a) = Fkl k a (insertMinQEager mini miniv empty l)
-- TODO: Make list fusion work.
{-# INLINE fromDescKVList #-}
