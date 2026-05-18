module Lists where

import Data.List
import Data.Ord


prefix :: [a]-> [[a]]
prefix ns = [take i ns | i <- [0..(length ns)]]

suffix :: [a] -> [[a]]
suffix ns = [drop i ns | i <- [0..(length ns)]]

interleave :: a -> [a] -> [[a]]
interleave n ms = [ ls ++ n : rs | (ls, rs) <- zip (prefix ms) (suffix ms)] 

permutation :: [a] -> [[a]]
permutation [] = [[]]
permutation (n : ns) = [ms | ls <- permutation ns, ms <- interleave n ls]



powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (n : ns) = [n : ms | ms <- powerset ns] ++ powerset ns

partitions :: [a] -> [[[a]]]
partitions [] = [[]]
partitions (n : ns) = [[n] : mss | mss <- partitions ns] ++ [lss | mss <- partitions ns, lss <- addEach n mss ]

addEach :: a -> [[a]] -> [[[a]]]
addEach n [] = []
addEach n (ns : nss) = ((n : ns) : nss) : [ns : lss | lss <- addEach n nss]

partitionsWithOrders :: [a] -> [[[a]]]
partitionsWithOrders ns = [lss | mss <- partitions ns, lss <- permutation mss]


pairsSlanting :: [a] -> [(a,a)]
pairsSlanting xs = [ p | n <- [0..((length xs * 2) - 1)], p <- slanting xs n ]
  where slanting xs0 n0 = zip (part xs0 n0) (reverse (part xs0 n0))
        part xs1 n1 | n1 <= length xs1  = take n1 xs
                    | otherwise         = drop (n1 - length xs1) xs


-- grouping [(1,"A"), (1, "B"), (2, "C")] = [["A","B"],["C"]]
grouping :: Eq a => [(a,b)] -> [[b]]
grouping [] = []
grouping ((x, y) : a) = (y : [ y' | (_, y') <- a1 ]) : grouping a2
  where (a1, a2) = partition (\(x', _) -> x == x') a

removeAt :: Int -> [a] -> [a]
removeAt n as = take n as ++ drop (n + 1) as


-- filterOut [(1,2), (1,3), (2,4), (3,3), (1,4), (3,1)] = [(2,4),(1,4),(3,1)]
-- (remove pairs with same 1st element)
filterOut :: Eq a => [(a, b)] -> [(a, b)]
filterOut [] = []
filterOut ((x, y) : ps)
  | Just _ <- lookup x ps = filterOut ps
  | otherwise             = (x, y) : filterOut ps

  
cyclic :: [a] -> [a]
cyclic [] = []
cyclic (x : xs) = x : cyclic( xs ++ [x] )


-- e.g. commonFirstElements [(1,2), (1,4), (1,3)] = True
commonFirstElements :: Eq a => [(a, a)] -> Bool
commonFirstElements ((x1, y1) : (x2, y2) : xps) 
  | x1 == x2   = commonFirstElements ((x2, y2) : xps)
  | otherwise  = False
commonFirstElements xps = True



-- e.g. takeEach [[1,2,3], [a,b,c], [A,B,C]] = [[1,a,A], [1,a,B], [1,a,C], [1,b,A], ...]
takeEach :: [[a]] -> [[a]]
takeEach [] = [[]]
takeEach (xs : xss) = [ x : ys | ys <- takeEach xss, x <- xs]