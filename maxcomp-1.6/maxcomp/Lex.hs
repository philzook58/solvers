module Lex where

gtLex :: Eq a => (a -> a -> Bool) -> [a] -> [a] -> Bool
gtLex _  []       []       = False
gtLex gt (x : xs) (y : ys) = gt x y || (x == y && gtLex gt xs ys)
gtLex _ _ _ = error "gtLex"
