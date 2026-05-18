module Indexing where
-- fingerprint indexing due to Schulz (IJCAR 2012)

import qualified Data.IntMap.Strict as IM
import qualified Data.Vector as V
import Data.Maybe

import Term
import Signature

-- assumption: function symbols are represented by non-negative integers.
-- A = -1
-- B = -2
-- N = -3
type Feature = Int
a :: Int
a = -1
b :: Int
b = -2
n :: Int
n = -3

-- general fingerprint feature function
gfpf :: Term -> Position -> Feature
gfpf (V _) [] = a
gfpf (V _) _ = b
gfpf (F f _) [] = f
gfpf (F _ ts) (i : ps)
  | i < 0 = error "gfpf: position must not contain negative integer (bug)"
  | i >= length ts = n
  | otherwise = gfpf (ts !! i) ps

fp :: Term -> [Position] -> [Feature]
fp t ps = [ gfpf t p | p <- ps ]

-- matching compatibility to f (e.g., f is a feature of a matchee)
matchingCompatiblesTo :: Signature -> Feature -> [Feature]
matchingCompatiblesTo sig f
  | V.length sig <= f = error ("matchingCompatiblesTo: too large feature (bug)")
  | 0 <= f = [f, a, b]
  | f == a = [a, b]
  | f == b = [b]
  | f == n = [b, n]
  | otherwise = error ("matchingCompatiblesTo: feature must be >= -3 (bug)")

unificationCompatibles :: Signature -> Feature -> [Feature]
unificationCompatibles sig f
  | V.length sig <= f = error ("unificationCompatibles: too large feature (bug)")
  | 0 <= f = [f, a, b]
  | f == a = a : b : [0..(V.length sig - 1)]
  | f == b = a : b : n : [0..(V.length sig - 1)]
  | f == n = [b, n]
  | otherwise = error ("unificationCompatibles: feature must be >= -3 (bug)")

-- Index is a trie-like structure to accelerate matching and unification
-- assumed to be a constant-depth tree
data Index a = Leaf [a] | Node (IM.IntMap (Index a))
  deriving Show

-- TODO: we have a problem with fp0 = []
empty :: Index a
empty = Node (IM.empty)

singleton :: a -> [Feature] -> Index a
singleton x [] = Leaf [x]
singleton x (f : fs) = Node (IM.singleton f (singleton x fs))

insert :: a -> [Feature] -> Index a -> Index a
insert x [] (Leaf ys) = Leaf (x : ys)
insert _ _ (Leaf _) = error "insert: too long feature vector is provided (bug)"
insert _ [] (Node _) = error "insert: too short feature vector is provided (bug)"
insert x (f : fs) (Node m) = Node (IM.insertWith recur f (singleton x fs) m)
  where
    recur _ ind = insert x fs ind

retrieve :: (Feature -> [Feature]) -> [Feature] -> Index a -> [a]
retrieve getCompats = retrieve'
  where  
    retrieve' [] (Leaf as) = as
    retrieve' _ (Leaf _) = error "retrieve: too long feature vector is provided (bug)"
    retrieve' [] (Node _) = error "retrieve: too short feature vector is provided (bug)"
    retrieve' (f : fs) (Node m) =
      concat [ retrieve' fs ind | g <- getCompats f, ind <- maybeToList (IM.lookup g m) ]

retrieveMatchers, retrieveUnifiables :: Signature -> [Feature] -> Index a -> [a]
retrieveMatchers sig = retrieve (matchingCompatiblesTo sig)
retrieveUnifiables sig = retrieve (unificationCompatibles sig)

toList :: Index a -> [a]
toList (Leaf xs) = xs
toList (Node m) = concat [ toList ind | (_, ind) <- IM.toList m ] 

-- see Schulz (IJCAR 2012)
-- note that our positions are 0-indexed
fp1, fp2, fp3d, fp4m, fp5m, fp6m, fp7, fp8x2 :: [Position]
-- fp0 = [ ]
fp1 = [ [] ]
fp2 = [ [], [0] ]
fp3d = [ [], [0], [0,0] ]
fp4m = [ [], [0], [1], [0,0] ]
fp5m = [ [], [0], [1], [2], [0, 0] ]
fp6m = [ [], [0], [1], [2], [0, 0], [0, 1] ]
fp7 = [ [], [0], [1], [2], [0, 0], [0, 1], [1, 0], [1, 1] ]
fp8x2 = [ [], [0], [1], [2], [3], [0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2], [0, 0, 0], [1, 0, 0] ]

parse :: String -> [Position]
-- parse "0" = fp0
parse "1" = fp1
parse "2" = fp2
parse "3d" = fp3d
parse "4m" = fp4m
parse "5m" = fp5m
parse "6m" = fp6m
parse "7" = fp7
parse "8x2" = fp8x2
parse _ = error "unknown fingerprint shape"
