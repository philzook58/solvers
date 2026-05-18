module Signature where

import qualified Data.Vector as V
import Data.Text

type Signature = V.Vector (Text, Int) -- (name, arity)

arity :: Signature -> Int -> Int 
arity sig f = snd (sig V.! f)

name :: Signature -> Int -> Text
name sig f = fst (sig V.! f)

findId :: Signature -> Text -> Int
findId sig f
  | Just i <- V.findIndex (\(g, _) -> f == g) sig = i
  | otherwise = error ("id: not found")

constants :: Signature -> [Int]
constants sig = 
  [ i | (i, (_, 0)) <- V.toList (V.indexed sig) ]

unaries :: Signature -> [Int]
unaries sig =
  [ i | (i, (_, 1)) <- V.toList (V.indexed sig) ]
