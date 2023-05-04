{- options_ghc -ddump-simpl #-}

module Bootstrapped where
--import qualified Prio as P
--import qualified Data.Foldable as Foldable
import qualified Loop as P
import Prelude hiding (null)

-- Conceptually, a MinPQueue of nonempty, unsized bootstrapped
-- queues. We need this for its recursion; hence the terrible
-- name.
--newtype Loop a = Loop { unLoop :: P.MinPQueue a (Loop a) }

data MinQueue a
  = Empty
  | Full !Int !a !(P.Loop a)

empty :: MinQueue a
empty = Empty

null :: MinQueue a -> Bool
null Empty = True
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
insert a Empty = Full 1 a P.empty
insert a (Full sz b q)
  | a <= b
  = Full (sz + 1) a (P.insert b P.empty q)
  | otherwise
  = Full (sz + 1) b (P.insert a P.empty q)

merge :: Ord a => MinQueue a -> MinQueue a -> MinQueue a
merge Empty q = q
merge p Empty = p
merge (Full sz1 a1 q1) (Full sz2 a2 q2)
  | a1 <= a2
  = Full sz a1 (P.insert a2 q2 q1)
  | otherwise
  = Full sz a2 (P.insert a1 q1 q2)
  where
    !sz = sz1 + sz2

minView :: Ord a => MinQueue a -> Maybe (a, MinQueue a)
minView Empty = Nothing
minView (Full sz a q) = Just (a, rebuild (sz - 1) q)

-- | Takes the number of elements stored in a looped queue and
-- the looped queue and produces a `MinQueue`.
rebuild :: Ord a => Int -> P.Loop a -> MinQueue a
rebuild !sz q = case P.minViewWithKey q of
  Nothing -> Empty
  Just ((b, z), q') ->
    Full sz b (P.merge z q')
    -- We use z as the first operand because it will be Nil if b was inserted
    -- rather than merged in. Since merge inspects its first operand first, GHC
    -- will likely preserve that behavior and make this common case slightly
    -- cheaper.
    --
    -- Should we use P.mergeEager instead of P.merge? I don't know. We can
    -- certainly afford it for big O, but it adds work to what's already the
    -- most expensive basic operation. Some *relevant* benchmarks would be
    -- nice.

size :: MinQueue a -> Int
size Empty = 0
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

-- | Convert a 'P.Loop' to a 'MinQueue', given the total number of
-- elements stored in the 'Loop'.
fromLoop :: Ord a => Int -> P.Loop a -> MinQueue a
fromLoop !s q = case P.minViewWithKey q of
  Nothing -> Empty
  Just ((k, qq), q') -> Full s k (P.mergeEager qq q')

instance (Show a, Ord a) => Show (MinQueue a) where
  showsPrec p = showsPrec p . toList
