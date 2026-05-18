module IntMultiSet where
-- multiset of integers based on IntMap.
-- The implementation and API follow those of Data.MultiSet.

import qualified Data.IntMap.Strict as IM
import Data.List (foldl')

type IntMultiSet = IM.IntMap Int

empty :: IntMultiSet
empty = IM.empty

insert :: Int -> IntMultiSet -> IntMultiSet
insert x = IM.insertWith (+) x 1

singleton :: Int -> IntMultiSet
singleton x = insert x empty

occur :: Int -> IntMultiSet -> Int
occur x = IM.findWithDefault 0 x

union :: IntMultiSet -> IntMultiSet -> IntMultiSet
union m1 m2 = IM.unionWith (+) m1 m2

unions :: [IntMultiSet] -> IntMultiSet
unions ms = foldl' union empty ms

isSubsetOf :: IntMultiSet -> IntMultiSet -> Bool
isSubsetOf m1 m2 = IM.isSubmapOfBy (<=) m1 m2
