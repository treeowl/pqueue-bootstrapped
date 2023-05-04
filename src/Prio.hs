{-# options_ghc -ddump-simpl #-}
module Prio where
import Prelude hiding (null)

data Tree rk k a = Tree !k !(rk k a)
data Forest rk k a
  = Skip (Forest (Succ rk) k a)
  | Cons {-# UNPACK #-} !(Tree rk k a) (Forest (Succ rk) k a)
  | Nil
data Succ rk k a = Succ {-# UNPACK #-} !(Tree rk k a) !(rk k a)
newtype Zero k a = Zero a

type BinomHeap = Forest Zero

-- | Priority queues strict in both keys and values.
newtype MinPQueue k a = MinPQ (BinomHeap k a)

null :: MinPQueue k a -> Bool
null (MinPQ Nil) = True
null _ = False

tip :: k -> a -> Tree Zero k a
tip k a = Tree k (Zero a)
{-# INLINE tip #-}

empty :: MinPQueue k a
empty = MinPQ Nil

insert :: Ord k => k -> a -> MinPQueue k a -> MinPQueue k a
insert k a (MinPQ q) = MinPQ (incr (tip k a) q)

insertEager :: Ord k => k -> a -> MinPQueue k a -> MinPQueue k a
insertEager k a (MinPQ q) = MinPQ (incr' (tip k a) q)

incr :: Ord k => Tree rk k a -> Forest rk k a -> Forest rk k a
incr t Nil = Cons t Nil
incr t (Skip f) = Cons t f
incr t1 (Cons t2 !f) = Skip $ incr (joinBin t1 t2) f

incr' :: Ord k => Tree rk k a -> Forest rk k a -> Forest rk k a
incr' t Nil = Cons t Nil
incr' t (Skip f) = Cons t f
incr' t1 (Cons t2 !f) = Skip $! incr' (joinBin t1 t2) f

joinBin :: Ord k => Tree rk k a -> Tree rk k a -> Tree (Succ rk) k a
joinBin t1@(Tree k1 rk1) t2@(Tree k2 rk2)
  | k1 <= k2
  = Tree k1 (Succ t2 rk1)
  | otherwise
  = Tree k2 (Succ t1 rk2)

-- | Amortized \(O(\log(\min(m,n)))\), worst case \(O(\log(\max(m,n)))\).
-- Merge two queues.
merge :: Ord k => MinPQueue k a -> MinPQueue k a -> MinPQueue k a
merge (MinPQ p) (MinPQ q) = MinPQ (mergeF p q)

mergeF :: Ord k => Forest rk k a -> Forest rk k a -> Forest rk k a
mergeF Nil q = q
mergeF p Nil = p
mergeF (Skip ts) (Skip us) = Skip $! mergeF ts us
mergeF (Skip ts) (Cons u us) = Cons u $! mergeF ts us
mergeF (Cons t ts) (Skip us) = Cons t $! mergeF ts us
mergeF (Cons t ts) (Cons u us) = Skip $! carry (joinBin t u) ts us

carry :: Ord k => Tree rk k a -> Forest rk k a -> Forest rk k a -> Forest rk k a
carry t0 f1 f2 = t0 `seq` case (f1, f2) of
  (Skip f1', Skip f2')    -> Cons t0 $! mergeF f1' f2'
  (Skip f1', Cons t2 f2') -> Skip $! mergeCarry t0 t2 f1' f2'
  (Cons t1 f1', Skip f2') -> Skip $! mergeCarry t0 t1 f1' f2'
  (Cons t1 f1', Cons t2 f2')
        -> Cons t0 $! mergeCarry t1 t2 f1' f2'
  -- Why do these use incr and not incr'? We want the merge to take amortized
  -- O(log(min(|f1|, |f2|))) time. If we performed this final increment
  -- eagerly, that would degrade to O(log(max(|f1|, |f2|))) time.
  (Nil, _f2)              -> incr t0 f2
  (_f1, Nil)              -> incr t0 f1
  where
    mergeCarry tA tB = carry (tA `joinBin` tB)

-- | \(O(\log(\max(m,n)))\). Merge two queues without creating any
-- suspensions.
mergeEager :: Ord k => MinPQueue k a -> MinPQueue k a -> MinPQueue k a
mergeEager (MinPQ p) (MinPQ q) = MinPQ (mergeFEager p q)

mergeFEager :: Ord k => Forest rk k a -> Forest rk k a -> Forest rk k a
mergeFEager Nil q = q
mergeFEager p Nil = p
mergeFEager (Skip ts) (Skip us) = Skip $! mergeFEager ts us
mergeFEager (Skip ts) (Cons u us) = Cons u $! mergeFEager ts us
mergeFEager (Cons t ts) (Skip us) = Cons t $! mergeFEager ts us
mergeFEager (Cons t ts) (Cons u us) = Skip $! carryEager (joinBin t u) ts us

carryEager :: Ord k => Tree rk k a -> Forest rk k a -> Forest rk k a -> Forest rk k a
carryEager t0 f1 f2 = t0 `seq` case (f1, f2) of
  (Skip f1', Skip f2')    -> Cons t0 $! mergeFEager f1' f2'
  (Skip f1', Cons t2 f2') -> Skip $! mergeCarry t0 t2 f1' f2'
  (Cons t1 f1', Skip f2') -> Skip $! mergeCarry t0 t1 f1' f2'
  (Cons t1 f1', Cons t2 f2')
        -> Cons t0 $! mergeCarry t1 t2 f1' f2'
  (Nil, _f2)              -> incr' t0 f2
  (_f1, Nil)              -> incr' t0 f1
  where
    mergeCarry tA tB = carryEager (tA `joinBin` tB)

-- | \(O(\log n)\). The number of elements in the queue.
size :: MinPQueue k a -> Int 
size (MinPQ hp) = go 0 1 hp
  where   
    go :: Int -> Int -> Forest rk k a -> Int
    go acc rk Nil = rk `seq` acc
    go acc rk (Skip f) = go acc (2 * rk) f
    go acc rk (Cons _t f) = go (acc + rk) (2 * rk) f


data Extract rk k a = Extract !k (rk k a) !(Forest rk k a)
data MExtract rk k a = No | Yes {-# UNPACK #-} !(Extract rk k a)

incrExtract :: Extract (Succ rk) k a -> Extract rk k a
incrExtract (Extract minKey (Succ kChild kChildren) ts)
  = Extract minKey kChildren (Cons kChild ts)

incrExtract' :: Ord k => Tree rk k a -> Extract (Succ rk) k a -> Extract rk k a
incrExtract' t (Extract minKey (Succ kChild kChildren) ts)
  = Extract minKey kChildren (Skip $! incr' (t `joinBin` kChild) ts)

extractBin :: Ord k => Forest rk k a -> MExtract rk k a
extractBin = start
  where
    start :: Ord k => Forest rk k a -> MExtract rk k a
    start Nil = No
    start (Skip f) = case start f of
      No     -> No
      Yes ex -> Yes (incrExtract ex)
    start (Cons t@(Tree x ts) f) = Yes $ case go x f of
      No -> Extract x ts (skip f)
      Yes ex -> incrExtract' t ex

    go :: Ord k => k -> Forest rk k a -> MExtract rk k a
    go _min_above Nil = _min_above `seq` No
    go min_above (Skip f) = case go min_above f of
      No -> No
      Yes ex -> Yes (incrExtract ex)
    go min_above (Cons t@(Tree x ts) f)
      | min_above <= x = case go min_above f of
          No -> No
          Yes ex -> Yes (incrExtract' t ex)
      | otherwise = case go x f of
          No -> Yes (Extract x ts (skip f))
          Yes ex -> Yes (incrExtract' t ex)

-- | When the heap size is a power of two and we extract from it, we have
-- to shrink the spine by one. This function takes care of that.
skip :: Forest (Succ rk) k a -> Forest rk k a
skip Nil = Nil
skip f = Skip f
{-# INLINE skip #-}

minViewWithKey :: Ord k => MinPQueue k a -> Maybe ((k, a), MinPQueue k a)
minViewWithKey (MinPQ q) = case extractBin q of
  No -> Nothing
  Yes (Extract k (Zero a) q') -> Just ((k, a), MinPQ q')
{-# INLINE minViewWithKey #-}


data Ranky rk where
  Zeroy :: Ranky Zero
  Succy :: !(Ranky rk) -> Ranky (Succ rk)

mapWithKey :: forall k a b. (k -> a -> b) -> MinPQueue k a -> MinPQueue k b
mapWithKey f = \(MinPQ q) -> MinPQ $ go Zeroy q
  where
    go :: Ranky rk -> Forest rk k a -> Forest rk k b
    go !_ Nil = Nil
    go !rky (Skip rest) = Skip $ go (Succy rky) rest
    go !rky (Cons t rest) = Cons (goTree rky t) (go (Succy rky) rest)

    goTree :: Ranky rk -> Tree rk k a -> Tree rk k b
    goTree rky (Tree k ts) = Tree k (goRk k rky ts)
    {-# INLINE goTree #-}

    -- The first argument is the key that goes with the rightmost child.
    goRk :: k -> Ranky rk -> rk k a -> rk k b
    goRk !k Zeroy (Zero a) = Zero (f k a)
    goRk !k (Succy rky) (Succ t ts) = Succ (goTree rky t) (goRk k rky ts)
