{-# LANGUAGE BangPatterns #-}
module Loop where

import qualified Prio as P
import Data.Coerce
import qualified Data.Foldable as Foldable
import Prelude hiding (null)

-- | A priority queue holding keys of type @a@ and values of
-- type @Loop a@. This is kind of weird by itself, but implementing
-- priority queue operations for it lets us implement bootstrapped
-- queues (arguably) more cleanly.
newtype Loop a = Loop { unLoop :: P.MinPQueue a (Loop a) }

empty :: Loop a
empty = Loop P.empty

null :: Loop a -> Bool
null (Loop q) = P.null q

size :: Loop a -> Int
size (Loop q) = P.size q

insert :: Ord a => a -> Loop a -> Loop a -> Loop a
insert a l (Loop q) = Loop (P.insert a l q)

insertEager :: Ord a => a -> Loop a -> Loop a -> Loop a
insertEager a l (Loop q) = Loop (P.insertEager a l q)

minViewWithKey :: Ord a => Loop a -> Maybe ((a, Loop a), Loop a)
minViewWithKey (Loop q) = coerce $ P.minViewWithKey q

merge :: Ord a => Loop a -> Loop a -> Loop a
merge (Loop p) (Loop q) = Loop (P.merge p q)

mergeEager :: Ord a => Loop a -> Loop a -> Loop a
mergeEager (Loop p) (Loop q) = Loop (P.mergeEager p q)

-- | Convert a list of keys to a 'Loop', pairing each with an empty 'Loop'.
-- Return the 'Loop' and its size.
fromKeyList :: Ord a => [a] -> (Int, Loop a)
-- We calculate the size at the end rather than tracking it along the way; I'm
-- not sure which approach is better, but this way is simpler and should
-- be cheap enough, at least for non-tiny queues.
fromKeyList xs =
  let
    !q = Foldable.foldl' (\acc a -> insertEager a empty acc) empty xs
    !s = size q
  in (s, q)
