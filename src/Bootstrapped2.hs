{- options_ghc -ddump-simpl  #-}
module Bootstrapped2
  (
  -- * Type
    MinPQueue (Empty, (:<))

  -- * Basic operations
  , empty
  , singleton
  , insert
  , merge
  , null
  , minViewWithKey

  -- * List conversions
  , fromList
  , toList
  , fromAscList
  , fromDescList

  -- * Maps
  , mapWithKey
  , mapWithKey'
  , mapWithKey#

  -- * Traversals
  , traverseWithKey
  , mapMWithKey

  -- * Folds
  , foldrWithKey
  , foldlWithKey'
  , foldMapWithKey
  , traverseWithKey_

  -- * Unordered folds
  -- , foldrWithKeyU
  , foldMapWithKeyU
  , traverseWithKeyU
  ) where

import qualified Loop2 as P
import qualified Data.Foldable as Foldable
import Control.Applicative (liftA2)
import qualified GHC.Exts as Exts
import Data.Functor.WithIndex (FunctorWithIndex (..))
import Data.Foldable.WithIndex (FoldableWithIndex (..), itoList)
import Data.Traversable.WithIndex (TraversableWithIndex (..))
import Prelude hiding (null)

-- newtype Loop2 k a = Loop2 { unLoop2 :: P.MinPQueue2 k (Loop2 k a) a }

data MinPQueue k a
  = EmptyQ
  | Full !Int !k a !(P.Loop2 k a)

-- A Full node stores:
--
-- The queue size. Without that, calculating the size would be O(n)
--
-- A minimal key and its associated value.
--
-- A MinPQueue2. Each entry in the MinPQueue2 represents a nonempty
-- bootstrapped queue.

empty :: MinPQueue k a
empty = EmptyQ

singleton :: k -> a -> MinPQueue k a
singleton k a = Full 1 k a P.empty

null :: MinPQueue k a -> Bool
null EmptyQ = True
null _ = False

insert :: Ord k => k -> a -> MinPQueue k a -> MinPQueue k a
insert k a EmptyQ = Full 1 k a P.empty
insert k1 a1 (Full sz k2 a2 q)
  | k1 <= k2
  = Full (sz + 1) k1 a1 (P.insert k2 a2 P.empty q)
  | otherwise
  = Full (sz + 1) k2 a2 (P.insert k1 a1 P.empty q)

merge :: Ord k => MinPQueue k a -> MinPQueue k a -> MinPQueue k a
merge EmptyQ q = q
merge p EmptyQ = p
merge (Full sz1 k1 a1 q1) (Full sz2 k2 a2 q2)
  | k1 <= k2
  = Full sz k1 a1 (P.insert k2 a2 q2 q1)
  | otherwise
  = Full sz k2 a2 (P.insert k1 a1 q1 q2)
  where
    !sz = sz1 + sz2

-- | Convert a 'Loop2' of known size to a 'MinPQueue'.
-- Splitting this out makes inlining work out much more
-- nicely for some reason or other.
fromLoop :: Ord k => Int -> P.Loop2 k a -> MinPQueue k a
fromLoop sz q = case P.minViewWithKey q of
  Nothing -> EmptyQ
  Just ((k, b, z), q') -> Full sz k b (P.merge z q')

minViewWithKey :: Ord k => MinPQueue k a -> Maybe ((k, a), MinPQueue k a)
-- Ugh. I'd much rather have the result type be Maybe (k, a, MinPQueue k a),
-- but that would make it incompatible with other priority queue packages.
minViewWithKey EmptyQ = Nothing
minViewWithKey (Full sz j a q) = Just ((j, a), fromLoop (sz - 1) q)

size :: MinPQueue k a -> Int
size EmptyQ = 0
size (Full sz _ _ _) = sz

-- | Convert a queue to an ordered list.
toList :: Ord k => MinPQueue k a -> [(k,a)]
-- TODO: check if this gives us list fusion, and regardless, consider
-- doing it ourselves so we can get write-back rules.
toList = itoList

-- | Build a queue from a list of key-value pairs. If the keys are known
-- to be ascending or descending, it is more efficient to use
-- 'fromAscList' or 'fromDescList', respectively.
fromList :: Ord k => [(k, a)] -> MinPQueue k a
fromList xs = case P.fromKVList xs of
  (sz, q) -> fromLoop sz q

instance Functor (MinPQueue k) where
  fmap = mapWithKey . const

mapWithKey :: (k -> a -> b) -> MinPQueue k a -> MinPQueue k b
mapWithKey _f EmptyQ = EmptyQ
mapWithKey f (Full sz k a q) = Full sz k (f k a) (P.mapWithKey f q)

mapWithKey' :: (k -> a -> b) -> MinPQueue k a -> MinPQueue k b
mapWithKey' _f EmptyQ = EmptyQ
mapWithKey' f (Full sz k a q)
  | !b <- f k a
  = Full sz k b (P.mapWithKey' f q)

mapWithKey# :: (k -> a -> (# b #)) -> MinPQueue k a -> MinPQueue k b
mapWithKey# _f EmptyQ = EmptyQ
mapWithKey# f (Full sz k a q)
  | (# b #) <- f k a
  = Full sz k b (P.mapWithKey# f q)

{-# INLINABLE traverseWithKeyU #-}
-- | A traversal in no particular order.
traverseWithKeyU :: Applicative f => (k -> a -> f b) -> MinPQueue k a -> f (MinPQueue k b)
traverseWithKeyU _f EmptyQ = pure EmptyQ
traverseWithKeyU f (Full sz k a q) = liftA2 (\b q' -> Full sz k b q') (f k a) (P.traverseWithKeyU f q)

{-# INLINABLE foldMapWithKeyU #-}
foldMapWithKeyU :: Monoid m => (k -> a -> m) -> MinPQueue k a -> m
foldMapWithKeyU _f EmptyQ = mempty
foldMapWithKeyU f (Full _sz k a q) = f k a <> P.foldMapWithKeyU f q

instance (Ord k, Show k, Show a) => Show (MinPQueue k a) where
  showsPrec p = showsPrec p . toList

instance Ord k => Exts.IsList (MinPQueue k a) where
  type Item (MinPQueue k a) = (k, a)
  toList = toList
  fromList = fromList

instance Ord k => Semigroup (MinPQueue k a) where
  (<>) = merge

instance Ord k => Monoid (MinPQueue k a) where
  mempty = empty

-- | Build a queue from a list of key-value pairs whose keys are definitely
-- ascending. This precondition is not checked.
fromAscList :: [(k, a)] -> MinPQueue k a
fromAscList xs = case P.fromAscKVList xs of
  Nothing -> EmptyQ
  Just (sz, k, a, q) -> Full sz k a q

-- | Build a queue from a list of key-value pairs whose keys are definitely
-- descending. This precondition is not checked.
fromDescList :: [(k, a)] -> MinPQueue k a
fromDescList xs = case P.fromDescKVList xs of
  Nothing -> EmptyQ
  Just (sz, k, a, q) -> Full sz k a q

-- | Fold a queue lazily in key order.
foldrWithKey :: Ord k => (k -> a -> b -> b) -> b -> MinPQueue k a -> b
foldrWithKey f = \b xs -> go b xs
  where
    go b q = case minViewWithKey q of
      Nothing -> b
      Just ((k, v), q') -> f k v (go b q')

-- | Fold a queue strictly in key order.
foldlWithKey' :: Ord k => (b -> k -> a -> b) -> b -> MinPQueue k a -> b
foldlWithKey' f = \ b xs -> go b xs
  where
    go !b q = case minViewWithKey q of
      Nothing -> b
      Just ((k, v), q') -> go (f b k v) q'

-- | Traverse a queue in key order.
traverseWithKey :: (Applicative f, Ord k) => (k -> a -> f b) -> MinPQueue k a -> f (MinPQueue k b)
-- We're keeping track of the size here; it would probably be better not to do that.
traverseWithKey f = \xs -> go xs
  where
    go q = case minViewWithKey q of
      Nothing -> pure empty
      Just ((k, a), q') -> liftA2 (insertMinQ k) (f k a) (go q')

-- | Traverse a queue in key order, discarding the results.
traverseWithKey_ :: (Applicative f, Ord k) => (k -> a -> f b) -> MinPQueue k a -> f ()
traverseWithKey_ f = foldrWithKey (\k a r -> f k a *> r) (pure ())

-- | Fold a queue in key order.
foldMapWithKey :: (Ord k, Monoid m) => (k -> a -> m) -> MinPQueue k a -> m
foldMapWithKey = ifoldMap

-- | A version of 'traverseWithKey' that builds the result queue(s) as it goes.
mapMWithKey :: (Monad f, Ord k) => (k -> a -> f b) -> MinPQueue k a -> f (MinPQueue k b)
mapMWithKey f = \xs -> go empty xs
  where
    go !acc q = case minViewWithKey q of
      Nothing -> pure acc
      Just ((k, a), q') -> do
        b <- f k a
        go (insertMaxQ k b acc) q'

-- | Insert a key known to be at least as small as any in the queue. Warning:
-- this function both requires and maintains an additional data structure
-- invariant. It is safe to use this function to build up from an empty or
-- singleton queue, but it should not be used on an arbitrary queue.
insertMinQ :: k -> a -> MinPQueue k a -> MinPQueue k a
insertMinQ k a EmptyQ = singleton k a
insertMinQ k a (Full sz min_k min_v q) =
  Full (sz + 1) k a $ P.insertMinQ min_k min_v P.empty q

-- | Insert a key known to be at least as large as any in the queue. Warning:
-- this function both requires and maintains an additional data structure
-- invariant. It is safe to use this function to build up from an empty or
-- singleton queue, but it should not be used on an arbitrary queue.
insertMaxQ :: k -> a -> MinPQueue k a -> MinPQueue k a
insertMaxQ k a EmptyQ = singleton k a
insertMaxQ k a (Full sz min_k min_v q) =
  Full (sz + 1) min_k min_v $ P.insertMaxQ k a P.empty q

{-
-- TODO: Unordered folds.
foldrWithKeyU :: (k -> a -> b -> b) -> b -> MinPQueue k a -> b
foldrWithKeyU f = go
  where
    go b EmptyQ = b
    go b (Full _ min_key min_val q) = f min_key min_val $ P.foldrWithKeyU _ _ _
    -}

instance Ord k => Foldable (MinPQueue k) where
  foldr = foldrWithKey . const
  foldl' f = foldlWithKey' (\b _ a -> f b a)
  length = size
  null = null
  -- TODO: Add custom minimum and maximum using unordered folds.
  -- I'm a bit nervous about unordered sums and products, since those
  -- might not be commutative. Blech.
  {-
  minimum q = case foldlWithKeyU' go Nothing q of
    Nothing -> error "minimum: empty queue"
    Just r -> r
    where
      go Nothing a =
      -}

instance FunctorWithIndex k (MinPQueue k) where
  imap = mapWithKey

instance Ord k => FoldableWithIndex k (MinPQueue k) where
  -- ifoldMap takes the default using itraverse
  ifoldl' f = foldlWithKey' (\acc k a -> f k acc a)
  ifoldr = foldrWithKey

instance Ord k => Traversable (MinPQueue k) where
  traverse = traverseWithKey . const
  mapM = mapMWithKey . const

instance Ord k => TraversableWithIndex k (MinPQueue k) where
  itraverse = traverseWithKey

-- | A bidirectional pattern synonym for an empty priority queue.
--
-- @since 1.5.0
pattern Empty :: MinPQueue k a
pattern Empty = EmptyQ
# if __GLASGOW_HASKELL__ >= 902
{-# INLINE CONLIKE Empty #-}
# endif

infixr 5 :<

-- | A bidirectional pattern synonym for working with the minimum view of a
-- 'MinPQueue'. Using @:<@ to construct a queue performs an insertion in
-- \(O(1)\) amortized time. When matching on @(k, a) :< q@, forcing @q@ takes
-- \(O(\log n)\) time.
--
-- @since 1.5.0
pattern (:<) :: Ord k => (k, a) -> MinPQueue k a -> MinPQueue k a
pattern ka :< q <- (minViewWithKey -> Just (ka, q))
  where
    (k, a) :< q = insert k a q

{-# COMPLETE Empty, (:<) #-}
