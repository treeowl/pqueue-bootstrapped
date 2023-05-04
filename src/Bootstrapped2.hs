{- options_ghc -ddump-simpl  #-}
module Bootstrapped2 where
import qualified Loop2 as P
import qualified Data.Foldable as Foldable
import Data.Coerce
import Control.Applicative (liftA2)
import Prelude hiding (null)

-- newtype Loop2 k a = Loop2 { unLoop2 :: P.MinPQueue2 k (Loop2 k a) a }

data MinPQueue k a
  = Empty
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
empty = Empty

null :: MinPQueue k a -> Bool
null Empty = True
null _ = False

insert :: Ord k => k -> a -> MinPQueue k a -> MinPQueue k a
insert k a Empty = Full 1 k a P.empty
insert k1 a1 (Full sz k2 a2 q)
  | k1 <= k2
  = Full (sz + 1) k1 a1 (P.insert k2 a2 P.empty q)
  | otherwise
  = Full (sz + 1) k2 a2 (P.insert k1 a1 P.empty q)

merge :: Ord k => MinPQueue k a -> MinPQueue k a -> MinPQueue k a
merge Empty q = q
merge p Empty = p
merge (Full sz1 k1 a1 q1) (Full sz2 k2 a2 q2)
  | k1 <= k2
  = Full sz k1 a1 (P.insert k2 a2 q2 q1)
  | otherwise
  = Full sz k2 a2 (P.insert k1 a1 q1 q2)
  where
    !sz = sz1 + sz2

minViewWithKey :: Ord k => MinPQueue k a -> Maybe (k, a, MinPQueue k a)
minViewWithKey Empty = Nothing
minViewWithKey (Full sz j a q) = Just (j, a, newq)
  where
    newq = case P.minViewWithKey q of
             Nothing -> Empty
             Just ((k, b, z), q') -> Full (sz - 1) k b (P.merge z q')

size :: MinPQueue k a -> Int
size Empty = 0
size (Full sz _ _ _) = sz

toList :: Ord k => MinPQueue k a -> [(k,a)]
toList q = case minViewWithKey q of
  Nothing -> []
  Just (k, a, q') -> (k, a) : toList q'

fromList :: Ord k => [(k, a)] -> MinPQueue k a
fromList = Foldable.foldl' (flip (uncurry insert)) empty

mapWithKey :: (k -> a -> b) -> MinPQueue k a -> MinPQueue k b
mapWithKey _f Empty = Empty
mapWithKey f (Full sz k a q) = Full sz k (f k a) (coerce (P.mapWithKey f) q)

traverseWithKeyU :: Applicative f => (k -> a -> f b) -> MinPQueue k a -> f (MinPQueue k b)
traverseWithKeyU _f Empty = pure Empty
traverseWithKeyU f (Full sz k a q) = liftA2 (\b q' -> Full sz k b q') (f k a) (P.traverseWithKeyU f q)
