module ELPO where

import Term
import TRS
import Linear
import Precedence
import EKBO hiding (Parameter)
import Lex

type Parameter = (Linear.Algebra, Precedence)

showParameter :: Parameter -> String
showParameter (a, p) =
  "ELPO with interpretations on natural numbers\n\n" ++
  showAlgebra a ++
  "\nand precedence:\n\n" ++
  showPrecedence p ++ "\n"

-- LPO-based SPO

gtLPO123 :: TRS -> Parameter -> Term -> Term -> Bool
gtLPO123 table param s t =
  gtLPO12 table param s t || gtLPO3 table s t

gtLPO12 :: TRS -> Parameter -> Term -> Term -> Bool
gtLPO12 table (a, p) s@(F _ ss) t@(F _ ts) =
  (EKBO.gtB a p s t ||
   (EKBO.geqB a s t && gtLex (\s' t' -> elem (s', t') table) ss ts)) &&
  all (\t' -> elem (s, t') table) ts
gtLPO12 _ _ _ _  = False
  
gtLPO3 :: TRS -> Term -> Term -> Bool
gtLPO3 table (F _ ss) t = any (\s -> geqLPO table s t) ss
gtLPO3 _ _ _            = False

geqLPO :: TRS -> Term -> Term -> Bool
geqLPO table s t = s == t || elem (s, t) table

args :: Term -> [Term]
args (V _)    = []
args (F _ ts) = ts

gtLPO' :: TRS -> Parameter -> Term -> Term -> TRS
gtLPO' table param s t
  | elem (s, t) table         = table
  | gtLPO123 table2 param s t = (s, t) : table2
  | otherwise                 = table2
  where
    table1 = foldl (\tbl t' -> gtLPO' tbl param s t') table  (args t)
    table2 = foldl (\tbl s' -> gtLPO' tbl param s' t) table1 (args s)


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
  | gtLPO123 table param s t = makeTable ((s, t) : table) param es
  | otherwise               = makeTable table param es

gtLPO :: Parameter -> Term -> Term -> Bool
gtLPO param s t = 
  elem (s, t) (makeTable [] param (pairs s t))

-- LPO-based MSPO

gt :: Parameter -> Term -> Term -> Bool
gt param@(a, _) s t = 
  geqA a s t && gtLPO param s t
