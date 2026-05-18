{-# LANGUAGE OverloadedStrings #-}
module LPO where

import qualified Data.Text as T
import qualified Data.IntMap as IM

import Term
import qualified Precedence as Pr
import Signature
import qualified SPO
import qualified Algebra

type Param = Pr.Precedence

toSPOParam :: Param -> SPO.Param
toSPOParam prec = [Algebra.Precedence prec]

pp :: Signature -> Param -> T.Text
pp sig p = 
  "lexicographic path order\n" <>
  "precedence: " <> Pr.pp sig p

gt :: Param -> Term -> Term -> Bool
gt pr = SPO.gt (toSPOParam pr)

frequencyDesc, frequencyAsc :: Signature -> [Term] -> Param
frequencyDesc sig ts = Pr.frequencyDesc sig ts
frequencyAsc sig ts = Pr.frequencyAsc sig ts

-- skolemized LPO
-- IntMap specifies ordering between variables
-- variables are assumed to be smallest
gtSk :: IM.IntMap Int -> Param -> Term -> Term -> Bool
gtSk m _ (V x) (V y)
  | Just px <- IM.lookup x m, Just py <- IM.lookup y m = px > py
  | otherwise = False 
gtSk _ _ (V _) (F _ _) = False
gtSk _ _ (F _ _) (V _) = True
gtSk m pr s@(F f ss) t@(F g ts) =
  any (\si -> si == t || gtSk m pr si t) ss ||
  (all (\tj -> gtSk m pr s tj) ts &&
    (Pr.gt pr f g || (f == g && gtlex ss ts)))
  where
    gtlex [] _ = False
    gtlex (_ : _) [] = True
    gtlex (s' : ss') (t' : ts') = gtSk m pr s' t' || (s' == t' && gtlex ss' ts')
