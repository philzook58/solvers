module LPO where

import Data.List
import Term
import TRS
import Precedence
import Lex

-- Pretty printers

showParameter :: Precedence -> String
showParameter p =
  "LPO with precedence:\n\n" ++
  "  " ++ intercalate " > " p ++ "\n"

-- LPO

gtLPO123 :: TRS -> Precedence -> Term -> Term -> Bool
gtLPO123 table prec s t = 
  gtLPO12 table prec s t || gtLPO3 table s t

gtLPO12 :: TRS -> Precedence -> Term -> Term -> Bool
gtLPO12 table prec s@(F f ss) (F g ts) =
  (gtPrec prec f g ||
   (f == g && gtLex (\si ti -> elem (si, ti) table) ss ts)) &&
  all (\t -> elem (s, t) table) ts
gtLPO12 _ _ _ _  = False
  
gtLPO3 :: TRS -> Term -> Term -> Bool
gtLPO3 table (F _ ss) t = any (\s -> geqLPO table s t) ss
gtLPO3 _ _ _            = False

geqLPO :: TRS -> Term -> Term -> Bool
geqLPO table s t = s == t || elem (s, t) table

subtermsFromArgs :: Term -> [Term]
subtermsFromArgs t@(V _)    = [t]
subtermsFromArgs t@(F _ ts) =
  [ u | ti <- ts, u <- subtermsFromArgs ti ] ++ [t]

pairs :: Term -> Term -> TRS
pairs s t = 
  [ (s', t') | s' <- subtermsFromArgs s, t' <- subtermsFromArgs t ]

makeTable :: TRS -> Precedence -> TRS -> TRS
makeTable table _ [] = table
makeTable table prec ((s, t) : es)
  | gtLPO123 table prec s t = makeTable ((s, t) : table) prec es
  | otherwise               = makeTable table prec es

gtLPO :: Precedence -> Term -> Term -> Bool
gtLPO prec s t = elem (s, t) table
  where table = makeTable [] prec (pairs s t)
