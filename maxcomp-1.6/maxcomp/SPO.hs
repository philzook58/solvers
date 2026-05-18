module SPO where

import Term
import TRS
import Linear
import Precedence
import Lex

type Parameter = (Linear.Algebra, Linear.Algebra, Precedence)

showParameter :: Parameter -> String
showParameter (a1, a2, p) =
  "(M)SPO with two linear polynomial interpretations on natural numbers\n\n" ++
  "1st algebra\n" ++ showAlgebra a1 ++ "\n" ++
  "2nd algebra\n" ++ showAlgebra a2 ++ "\n" ++
  "\nand precedence:\n\n" ++
  showPrecedence p ++ "\n"

geqSq :: Parameter -> Term -> Term -> Bool
geqSq (a1, a2, p) s@(F f _) t@(F g _) =
  gtA a1 (markTerm s) (markTerm t) ||
  (geqA a1 (markTerm s) (markTerm t) && gtA a2 (markTerm s) (markTerm t)) ||
  (geqA a1 (markTerm s) (markTerm t) && geqA a2 (markTerm s) (markTerm t) && geqPrec p f g) 
geqSq _ s t = s == t

gtSq :: Parameter -> Term -> Term -> Bool
gtSq (a1, a2, p) s@(F f _) t@(F g _) =
  gtA a1 (markTerm s) (markTerm t) ||
  (geqA a1 (markTerm s) (markTerm t) && gtA a2 (markTerm s) (markTerm t)) ||
  (geqA a1 (markTerm s) (markTerm t) && geqA a2 (markTerm s) (markTerm t) && gtPrec p f g) 
gtSq _ _ _ = False

gtSPO123 :: TRS -> Parameter -> Term -> Term -> Bool
gtSPO123 table param s t =
  gtSPO12 table param s t || gtSPO3 table s t

gtSPO12 :: TRS -> Parameter -> Term -> Term -> Bool
gtSPO12 table param s@(F _ ss) t@(F _ ts) =
  (gtSq param s t ||
   (geqSq param s t && gtLex (\s' t' -> elem (s', t') table) ss ts)) &&
  all (\t' -> elem (s, t') table) ts
gtSPO12 _ _ _ _  = False

gtSPO3 :: TRS -> Term -> Term -> Bool
gtSPO3 table (F _ ss) t = any (\s -> geqSPO table s t) ss
gtSPO3 _ _ _            = False

geqSPO :: TRS -> Term -> Term -> Bool
geqSPO table s t = s == t || elem (s, t) table

args :: Term -> [Term]
args (V _)    = []
args (F _ ts) = ts

gtSPO' :: TRS -> Parameter -> Term -> Term -> TRS
gtSPO' table param s t
  | elem (s, t) table         = table
  | gtSPO123 table2 param s t = (s, t) : table2
  | otherwise                 = table2
  where
    table1 = foldl (\tbl t' -> gtSPO' tbl param s t') table  (args t)
    table2 = foldl (\tbl s' -> gtSPO' tbl param s' t) table1 (args s)

subtermsFromArgs :: Term -> [Term]
subtermsFromArgs t@(V _)    = [t]
subtermsFromArgs t@(F _ ts) =
  [ u | ti <- ts, u <- subtermsFromArgs ti ] ++ [t]

pairs :: Term -> Term -> TRS
pairs s t = 
  [ (s', t') | s' <- subtermsFromArgs s, t' <- subtermsFromArgs t ]

makeTable :: TRS -> Parameter -> TRS -> TRS
makeTable table _ [] = table
makeTable table param ((s, t) : es)
  | gtSPO123 table param s t = makeTable ((s, t) : table) param es
  | otherwise               = makeTable table param es

gtSPO :: Parameter -> Term -> Term -> Bool
gtSPO param s t = 
  elem (s, t) (makeTable [] param (pairs s t))

gt :: Parameter -> Term -> Term -> Bool
gt param@(a1, a2, _) s t = 
  geqA a1 s t && geqA a2 s t && gtSPO param s t
