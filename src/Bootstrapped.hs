{- options_ghc -ddump-simpl #-}
module Bootstrapped where

import qualified Loop as P
import Prelude hiding (null)
import qualified GHC.Exts as Exts
import Text.Read

-- Conceptually, a MinPQueue of nonempty, unsized bootstrapped
-- queues. We need this for its recursion; hence the terrible
-- name.
--newtype Loop a = Loop { unLoop :: P.MinPQueue a (Loop a) }

data MinQueue a
  = EmptyQ
  | Full !Int !a !(P.Loop a)

empty :: MinQueue a
empty = EmptyQ

singleton :: a -> MinQueue a
singleton a = Full 1 a P.empty

null :: MinQueue a -> Bool
null EmptyQ = True
null _ = False

insert :: Ord a => a -> MinQueue a -> MinQueue a
-- We always insert into the Loop of the given queue, rather than
-- inserting the given queue into a new Loop. Why is that? When
-- we insert a (nonempty) queue `p` into another queue `q` on merge,
-- we are essentially deferring the work of merging `p`. When we
-- eventually do merge `p`, we merge it not (necessarily) with `q`,
-- but rather with whatever `q` has grown or shrunk to. So inserting
-- `p` into an /empty/ queue could generate up to O(log p) work for
-- a future extraction. Of course, this could potentially make
-- extractions before that go faster, but I think that's almost
-- certainly a bad trade-off.
insert a EmptyQ = Full 1 a P.empty
insert a (Full sz b q)
  | a <= b
  = Full (sz + 1) a (P.insert b P.empty q)
  | otherwise
  = Full (sz + 1) b (P.insert a P.empty q)

merge :: Ord a => MinQueue a -> MinQueue a -> MinQueue a
merge EmptyQ q = q
merge p EmptyQ = p
merge (Full sz1 a1 q1) (Full sz2 a2 q2)
  | a1 <= a2
  = Full sz a1 (P.insert a2 q2 q1)
  | otherwise
  = Full sz a2 (P.insert a1 q1 q2)
  where
    !sz = sz1 + sz2

minView :: Ord a => MinQueue a -> Maybe (a, MinQueue a)
minView EmptyQ = Nothing
minView (Full sz a q) = Just (a, fromLoop (sz - 1) q)

size :: MinQueue a -> Int
size EmptyQ = 0
size (Full sz _ _) = sz

{-# INLINABLE toList #-}
toList :: Ord a => MinQueue a -> [a]
toList q = case minView q of
  Nothing -> []
  Just (a, q') -> a : toList q'

fromList :: Ord a => [a] -> MinQueue a
-- We go to some trouble to avoid the unneeded comparisons that
-- would come from the obvious insertion fold. Instead of checking
-- each element against the minimum so far, we just insert them
-- all and pull the minimum out at the end.
fromList xs = let !(!s, !q) = P.fromKeyList xs
  in fromLoop s q

fromAscList :: [a] -> MinQueue a
fromAscList xs = case P.fromAscKeyList xs of
  Nothing -> EmptyQ
  Just (sz, a, q) -> Full sz a q

fromDescList :: [a] -> MinQueue a
fromDescList xs = case P.fromDescKeyList xs of
  Nothing -> EmptyQ
  Just (sz, a, q) -> Full sz a q

-- | Convert a 'P.Loop' to a 'MinQueue', given the total number of
-- elements stored in the 'Loop'.
fromLoop :: Ord a => Int -> P.Loop a -> MinQueue a
fromLoop !s q = case P.minViewWithKey q of
  Nothing -> EmptyQ
  Just ((k, qq), q') -> Full s k (P.merge qq q')
  -- Should we use P.mergeEager instead of P.merge? I don't know. We can
  -- certainly afford it for big O, but it adds work to what's already the
  -- most expensive basic operation. Some *relevant* benchmarks would be
  -- nice.
  --
  -- We use qq as the first operand because it will be Nil if k was inserted
  -- rather than merged in. Since merge inspects its first operand first, GHC
  -- will likely preserve that behavior and make this common case slightly
  -- cheaper.

-- | Queues are shown as lists.
instance (Show a, Ord a) => Show (MinQueue a) where
  showsPrec p = showsPrec p . toList

instance Ord a => Exts.IsList (MinQueue a) where
  type Item (MinQueue a) = a
  toList = toList
  fromList = fromList

instance Ord a => Semigroup (MinQueue a) where
  (<>) = merge

instance Ord a => Monoid (MinQueue a) where
  mempty = empty

-- | Queues are read as lists.
instance (Read a, Ord a) => Read (MinQueue a) where
  -- As usual, we build an underlying Loop first to avoid O(n) extra
  -- key comparisons in typical cases.
  readPrec = do
    (sz, q) <- P.readLoop
    pure $! fromLoop sz q

-- | A bidirectional pattern synonym for an empty priority queue.
--
-- @since 1.5.0
pattern Empty :: MinQueue a
pattern Empty = EmptyQ
#if __GLASGOW_HASKELL__ >= 902
{-# INLINE CONLIKE Empty #-}
#endif

infixr 5 :<

-- | A bidirectional pattern synonym for working with the minimum view of a
-- 'MinPQueue'.  Using @:<@ to construct a queue performs an insertion in
-- \(O(1)\) amortized time. When matching on @a :< q@, forcing @q@ takes
-- \(O(\log n)\) time.
pattern (:<) :: Ord a => a -> MinQueue a -> MinQueue a
pattern a :< q <- (minView -> Just (a, q))
  where
    a :< q = insert a q

{-# COMPLETE Empty, (:<) #-}
