{- options_ghc -ddump-simpl -dsuppress-type-applications -dsuppress-coercions #-}
{-# LANGUAGE BangPatterns #-}
module Loop where

import qualified Prio as P
import Data.Coerce
import qualified Data.Foldable as Foldable
import Prelude hiding (null)
import Text.Read
import qualified Text.ParserCombinators.ReadPrec as ReadPrec
import qualified Text.ParserCombinators.ReadP as ReadP

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

-- | Convert an ascending list of keys to a 'Loop', pairing each with an empty 'Loop'.
-- Return the 'Loop' and its size, along with the minimum element.
fromAscKeyList :: [a] -> Maybe (Int, a, Loop a)
-- We calculate the size at the end rather than tracking it along the way; I'm
-- not sure which approach is better, but this way is simpler and should
-- be cheap enough, at least for non-tiny queues.
fromAscKeyList xs = case Foldable.foldl' go NoFkl xs of
  NoFkl -> Nothing
  Fkl the_min q ->
    let !s = size q + 1
    in Just (s, the_min, q)
  where
    go NoFkl a = Fkl a empty
    go (Fkl mini l) a = Fkl mini (insertMaxQEager a empty l)
-- TODO: We actually want to get list fusion. Currently, that's not
-- happening. Let's figure out how to fix that.
{-# INLINE fromAscKeyList #-}

insertMaxQEager :: a -> Loop a -> Loop a -> Loop a
insertMaxQEager k v (Loop q) = Loop (P.insertMaxQEager k v q)

insertMinQEager :: a -> Loop a -> Loop a -> Loop a
insertMinQEager k v (Loop q) = Loop (P.insertMinQEager k v q)

data Fkl a = NoFkl | Fkl !a !(Loop a)

-- | Convert a descending list of keys to a 'Loop', pairing each with an empty 'Loop'.
-- Return the 'Loop' and its size, along with the minimum element.
fromDescKeyList :: [a] -> Maybe (Int, a, Loop a)
-- We calculate the size at the end rather than tracking it along the way; I'm
-- not sure which approach is better, but this way is simpler and should
-- be cheap enough, at least for non-tiny queues.
fromDescKeyList xs = case Foldable.foldl' go NoFkl xs of
  NoFkl -> Nothing
  Fkl the_min q ->
    let !s = size q + 1
    in Just (s, the_min, q)
  where
    go NoFkl a = Fkl a empty
    go (Fkl mini l) a = Fkl a (insertMinQEager mini empty l)
{-# INLINE fromDescKeyList #-}

-- This is used to implement `readPrec` for bootstrapped queues. Interleaving
-- insertion with parsing saves a good bit of time (maybe 40% or so)
-- when reading a queue of Ints, compared to reading the list and then
-- converting it to a queue.
--
-- The number of elements read is returned alongside the loop.
readLoop :: (Ord a, Read a) => ReadPrec (Int, Loop a)
readLoop =
  parens
  ( do '[' <- ReadPrec.get
       (listRest False empty +++ listNext empty)
  )
 where
  listRest started !q =
    do ReadPrec.lift ReadP.skipSpaces
       c <- ReadPrec.get
       case c of
         ']'           -> return $! ((,) $! size q) q
         ',' | started -> listNext q
         _             -> pfail

  listNext !q =
    do x  <- reset readPrec
       listRest True (insert x empty q)
