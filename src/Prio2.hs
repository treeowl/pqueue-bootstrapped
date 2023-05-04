{- options_ghc -ddump-simpl #-}
module Prio2 where
import Prelude hiding (null)
import Control.Applicative (liftA2)
import GHC.Exts (inline)

-- The 'q' value associated with a key is its rightmost child.
data Tree rk k q a = Tree !k a !(rk k q a)
data Forest rk k q a
  = Skip (Forest (Succ rk) k q a)
  | Cons {-# UNPACK #-} !(Tree rk k q a) (Forest (Succ rk) k q a)
  | Nil
data Succ rk k q a = Succ {-# UNPACK #-} !(Tree rk k q a) !(rk k q a)
newtype Zero k q a = Zero q

type BinomHeap = Forest Zero

-- | Priority queues strict in both keys and values.
newtype MinPQueue2 k q a = MinPQ (BinomHeap k q a)

null :: MinPQueue2 k q a -> Bool
null (MinPQ Nil) = True
null _ = False

tip :: k -> a -> q -> Tree Zero k q a
tip k a q = Tree k a (Zero q)
{-# INLINE tip #-}

empty :: MinPQueue2 k q a
empty = MinPQ Nil

insert :: Ord k => k -> a -> q -> MinPQueue2 k q a -> MinPQueue2 k q a
insert k a qq (MinPQ q) = MinPQ (incr (tip k a qq) q)

insertEager :: Ord k => k -> a -> q -> MinPQueue2 k q a -> MinPQueue2 k q a
insertEager k a qq (MinPQ q) = MinPQ (incr' (tip k a qq) q)

incr :: Ord k => Tree rk k q a -> Forest rk k q a -> Forest rk k q a
incr t Nil = Cons t Nil
incr t (Skip f) = Cons t f
incr t1 (Cons t2 !f) = Skip $ incr (joinBin t1 t2) f

incr' :: Ord k => Tree rk k q a -> Forest rk k q a -> Forest rk k q a
incr' t Nil = Cons t Nil
incr' t (Skip f) = Cons t f
incr' t1 (Cons t2 !f) = Skip $! incr' (joinBin t1 t2) f

joinBin :: Ord k => Tree rk k q a -> Tree rk k q a -> Tree (Succ rk) k q a
joinBin t1@(Tree k1 a1 rk1) t2@(Tree k2 a2 rk2)
  | k1 <= k2
  = Tree k1 a1 (Succ t2 rk1)
  | otherwise
  = Tree k2 a2 (Succ t1 rk2)

merge :: Ord k => MinPQueue2 k q a -> MinPQueue2 k q a -> MinPQueue2 k q a
merge (MinPQ p) (MinPQ q) = MinPQ (mergeF p q)

mergeF :: Ord k => Forest rk k q a -> Forest rk k q a -> Forest rk k q a
mergeF Nil q = q
mergeF p Nil = p
mergeF (Skip ts) (Skip us) = Skip $! mergeF ts us
mergeF (Skip ts) (Cons u us) = Cons u $! mergeF ts us
mergeF (Cons t ts) (Skip us) = Cons t $! mergeF ts us
mergeF (Cons t ts) (Cons u us) = Skip $! mergeF (incr (joinBin t u) ts) us

-- TODO: size in O(log n), but that's not useful for bootstrapping, so it's
-- not a priority.

data Extract rk k q a = Extract !k a (rk k q a) !(Forest rk k q a)
data MExtract rk k q a = No | Yes {-# UNPACK #-} !(Extract rk k q a)

incrExtract :: Extract (Succ rk) k q a -> Extract rk k q a
incrExtract (Extract minKey minVal (Succ kChild kChildren) ts)
  = Extract minKey minVal kChildren (Cons kChild ts)

incrExtract' :: Ord k => Tree rk k q a -> Extract (Succ rk) k q a -> Extract rk k q a
incrExtract' t (Extract minKey minVal (Succ kChild kChildren) ts)
  = Extract minKey minVal kChildren (Skip $! incr' (t `joinBin` kChild) ts)

extractBin :: Ord k => Forest rk k q a -> MExtract rk k q a
extractBin = start
  where
    start :: Ord k => Forest rk k q a -> MExtract rk k q a
    start Nil = No
    start (Skip f) = case start f of
      No     -> No
      Yes ex -> Yes (incrExtract ex)
    start (Cons t@(Tree x a ts) f) = Yes $ case go x f of
      No -> Extract x a ts (skip f)
      Yes ex -> incrExtract' t ex

    go :: Ord k => k -> Forest rk k q a -> MExtract rk k q a
    go _min_above Nil = _min_above `seq` No
    go min_above (Skip f) = case go min_above f of
      No -> No
      Yes ex -> Yes (incrExtract ex)
    go min_above (Cons t@(Tree x a ts) f)
      | min_above <= x = case go min_above f of
          No -> No
          Yes ex -> Yes (incrExtract' t ex)
      | otherwise = case go x f of
          No -> Yes (Extract x a ts (skip f))
          Yes ex -> Yes (incrExtract' t ex)

-- | When the heap size is a power of two and we extract from it, we have
-- to shrink the spine by one. This function takes care of that.
skip :: Forest (Succ rk) k q a -> Forest rk k q a
skip Nil = Nil
skip f = Skip f
{-# INLINE skip #-}

minViewWithKey :: Ord k => MinPQueue2 k q a -> Maybe ((k, a, q), MinPQueue2 k q a)
minViewWithKey (MinPQ q) = case extractBin q of
  No -> Nothing
  Yes (Extract k a (Zero qq) q') -> Just ((k, a, qq), MinPQ q')
{-# INLINE minViewWithKey #-}

-- | \(O(\log n)\). The number of elements in the queue.
size :: MinPQueue2 k q a -> Int
size (MinPQ hp) = go 0 1 hp
  where
    go :: Int -> Int -> Forest rk k q a -> Int
    go acc rk Nil = rk `seq` acc
    go acc rk (Skip f) = go acc (2 * rk) f
    go acc rk (Cons _t f) = go (acc + rk) (2 * rk) f

data Ranky rk where
  Zeroy :: Ranky Zero
  Succy :: !(Ranky rk) -> Ranky (Succ rk)

-- | An oddly specific mapping operation that works well for implementing
-- mapping for bootstrapped queues. This doesn't need the fancy plumbing that
-- the most natural general mapping operation would require, and it gets the
-- job done.
wonkyMap :: (k -> a -> b) -> (q -> r) -> MinPQueue2 k q a -> MinPQueue2 k r b
wonkyMap f g = inline wonkyMap# (\k a -> (# f k a #)) g

-- | A strict version of 'wonkyMap'.
wonkyMap' :: (k -> a -> b) -> (q -> r) -> MinPQueue2 k q a -> MinPQueue2 k r b
wonkyMap' f g = inline wonkyMap# (\k a -> let !b = f k a in (# b #)) g

wonkyMap# :: forall k a b q r. (k -> a -> (# b #)) -> (q -> r) -> MinPQueue2 k q a -> MinPQueue2 k r b
wonkyMap# f g = \(MinPQ q) -> MinPQ $ go Zeroy q
  where
    go :: Ranky rk -> Forest rk k q a -> Forest rk k r b
    go !_ Nil = Nil
    go !rky (Skip rest) = Skip $ go (Succy rky) rest
    go !rky (Cons t rest) = Cons (goTree rky t) (go (Succy rky) rest)

    goTree :: Ranky rk -> Tree rk k q a -> Tree rk k r b
    goTree rky (Tree k a ts)
      | (# b #) <- f k a = Tree k b (goRk rky ts)
    {-# INLINE goTree #-}

    goRk :: Ranky rk -> rk k q a -> rk k r b
    goRk Zeroy (Zero q) = Zero (g q)
    goRk (Succy rky) (Succ t ts) = Succ (goTree rky t) (goRk rky ts)

{-# INLINABLE wonkTrav #-}
wonkTrav :: forall k a b q r f w. Applicative f => (MinPQueue2 k r b -> w) -> (k -> a -> f b) -> (q -> f r) -> MinPQueue2 k q a -> f w
wonkTrav fin f g = \(MinPQ q) -> (fin . MinPQ) <$> go Zeroy q
  where
    go :: Ranky rk -> Forest rk k q a -> f (Forest rk k r b)
    go !_ Nil = pure Nil
    go !rky (Skip rest) = Skip <$> go (Succy rky) rest
    go !rky (Cons t rest) = liftA2 Cons (goTree rky t) (go (Succy rky) rest)

    goTree :: Ranky rk -> Tree rk k q a -> f (Tree rk k r b)
    goTree rky (Tree k a ts) = liftA2 (Tree k) (f k a) (goRk rky ts)
    {-# INLINE goTree #-}

    goRk :: Ranky rk -> rk k q a -> f (rk k r b)
    goRk Zeroy (Zero q) = Zero <$> g q
    goRk (Succy rky) (Succ t ts) = liftA2 Succ (goTree rky t) (goRk rky ts)
