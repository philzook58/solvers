module Linear where

import Data.List
import Term

type Value = (Int, [(String, Int)])

type Form = (Int, [Bool])

type Interpretation = (String, Form)

type Algebra = [Interpretation]

-- Pretty printers.

varX :: Int -> String
varX i = "x" ++ show i

showLinear :: Form -> String
showLinear (n, bs) =
  case ss1 ++ ss2 of
    [] -> "0"
    ss -> intercalate " + " ss
  where 
    ss1 = [ varX i | (i, True) <- zip [1..] bs ]
    ss2 = if n == 0 then [] else [ show n ]

showLHS :: (String, Int) -> String
showLHS (f, 0) = f ++ "_A"
showLHS (f, n) =
  f ++ "_A(" ++ intercalate "," [ varX i | i <- [1..n] ] ++ ")"

showInterpretation :: Interpretation -> String
showInterpretation (f, l@(_, bs)) =
  showLHS (f, length bs) ++ " = " ++ showLinear l

showAlgebra :: Algebra -> String
showAlgebra a =
  unlines [ "  " ++ showInterpretation l | l <- a ]

-- Arithmetic functions.

keys :: Eq a => [(a,b)] -> [a]
keys a = nub [ x | (x, _) <- a ]

zero :: Value
zero = (0, [])

variable :: String -> Value
variable x = (0, [(x, 1)])

constant :: Int -> Value
constant n = (n, [])

coefficient :: [(String, Int)] -> String -> Int
coefficient l x = Prelude.sum [ n | (y, n) <- l, x == y ]

add :: Value -> Value -> Value
add (n1, a1) (n2, a2) = (n1 + n2, [ (x, coefficient a x) | x <- keys a ])
  where 
    a = a1 ++ a2

sum :: [Value] -> Value
sum ls = foldr add zero ls

gt :: Value -> Value -> Bool
gt (n1, a1) (n2, a2) =
  n1 > n2 && 
  all (\x -> coefficient a1 x >= coefficient a2 x) (keys a2)

geq :: Value -> Value -> Bool
geq (n1, a1) (n2, a2) =
  n1 >= n2 && 
  all (\x -> coefficient a1 x >= coefficient a2 x) (keys a2)

interpret :: Algebra -> Term -> Value
interpret _ (V x) = variable x
interpret a (F f ts)
  | Just (n, bs) <- lookup f a =
    Linear.sum (constant n : [ interpret a t | (b, t) <- zip bs ts, b ])
  | otherwise = error ("interpret: " ++ show f ++ "\n" ++ show a)

gtA :: Algebra -> Term -> Term -> Bool
gtA a s t = gt (interpret a s) (interpret a t)

geqA :: Algebra -> Term -> Term -> Bool
geqA a s t = geq (interpret a s) (interpret a t)
