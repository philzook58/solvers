module OrderedRewriting where

import Terms
import Substitutions
import Rules
import Trie
import LPOTerminationCheck
import Debug.Trace
import Data.Ord
import Data.List


anOrderedReduct :: OTRST -> [String]  -> Term -> Maybe Term
anOrderedReduct otrst consts t
  | t' : _ <- allOrderedReducts otrst consts t  = Just t'
  | otherwise                                   = Nothing

anOrderedReductWithUsedRule :: OTRST -> [String]  -> Term -> Maybe (Term, Rule)
anOrderedReductWithUsedRule otrst consts t
  | tr : _ <- allOrderedReductsWithUsedRule otrst consts t  = Just tr
  | otherwise                                               = Nothing

allOrderedReducts :: OTRST -> [String]  -> Term -> [Term]
allOrderedReducts otrst consts t 
  = [ t' | (t', _) <- allOrderedReductsWithUsedRule otrst consts t ]

allOrderedReductsWithUsedRule :: OTRST -> [String]  -> Term -> [(Term, Rule)]
allOrderedReductsWithUsedRule ((es, trs, prec), trie) consts s  
  = [ (replace s (substitute v sgm') p, (u, v))
    | p <- allPositions s,
      er <- getMatchRules trie (subtermAt s p),
      (u, v) <- [ret er],
      Just sgm <- [match u (subtermAt s p)],
      sgm' <- [minimumSub er sgm],
      (isR er || orientable prec (substitute u sgm', substitute v sgm') ) ]
  where   
    minimumSub :: EquationOrRule -> Subst -> Subst
    minimumSub (E e) sgm  | Just minc <- minimumConstant prec consts  
                              = sgm ++ [ (x, F minc []) | x <- varsInEquation e, x `notElem` (domain sgm) ]
                          | otherwise 
                              = sgm
    minimumSub (R e) sgm = sgm
    ret (E e) = e
    ret (R r) = r
    isR (E _) = False
    isR (R _) = True

normalize :: OTRST -> [String] -> Term -> Term
-- normalize ((es, trs, _), _) consts t | es == []  = Rules.normalize trs t
normalize otrst consts t
  | Just t0 <- anOrderedReduct otrst consts t  = OrderedRewriting.normalize otrst consts t0
  | otherwise                                  = t

join :: OTRST -> [String] -> Term -> Term -> Bool
join otrst consts s t 
  = OrderedRewriting.normalize otrst consts s == OrderedRewriting.normalize otrst consts t

lrOrderedReduction :: OTRST -> [String] -> ES -> ES
lrOrderedReduction otrst consts es 
  = nubBy isSameEquation (removeTrivialEquations es')
    where es' = [ (OrderedRewriting.normalize otrst consts s, OrderedRewriting.normalize otrst consts t) 
                | (s, t) <- es ]




orient :: ES -> Precedence -> OTRS
orient es prec = (nubBy isSameEquation es2, nubBy isSameRule trs2, prec)
  where (es2, trs2) = orient1 es prec

orient1 :: ES -> Precedence -> (ES, TRS)
orient1 []            prec = ([], [])
orient1 ((s, t) : es) prec
  | s == t                 = (es2, trs2)
  | orientable prec (s, t) = (es2, (s, t) : trs2)
  | orientable prec (t, s) = (es2, (t, s) : trs2)
  | otherwise              = ((s, t) : es2, trs2)
  where
    (es2, trs2) = orient1 es prec








anExtendedOrderedReduct :: XOTRST -> [String]  -> Term -> Maybe Term
anExtendedOrderedReduct xotrst consts t
  | t' : _ <- allExtendedOrderedReducts xotrst consts t  = Just t'
  | otherwise                                   = Nothing

anExtendedOrderedReductWithUsedRule :: XOTRST -> [String]  -> Term -> Maybe (Term, Rule)
anExtendedOrderedReductWithUsedRule xotrst consts t
  | tr : _ <- allExtendedOrderedReductsWithUsedRule xotrst consts t  = Just tr
  | otherwise                                                        = Nothing

allExtendedOrderedReducts :: XOTRST -> [String]  -> Term -> [Term]
allExtendedOrderedReducts xotrst consts t 
  = [ t' | (t', _) <- allExtendedOrderedReductsWithUsedRule xotrst consts t ]


allExtendedOrderedReductsWithUsedRule :: XOTRST -> [String]  -> Term -> [(Term, Rule)]
allExtendedOrderedReductsWithUsedRule ((es, trs, precs@(prec : _)), trie) consts s  
  = [ (replace s (substitute v sgm') p, (u, v))
    | p <- allPositions s,
      er <- getMatchRules trie (subtermAt s p),
      (u, v) <- [ret er],
      Just sgm <- [match u (subtermAt s p)],
      sgm' <- [minimumSub er sgm],
      (isR er || ex_orientable precs (substitute u sgm', substitute v sgm') ) ]
  where   
    minimumSub :: EquationOrRule -> Subst -> Subst
    minimumSub (E e) sgm  | Just minc <- minimumConstant prec consts  
                              = sgm ++ [ (x, F minc []) | x <- varsInEquation e, x `notElem` (domain sgm) ]
                          | otherwise 
                              = sgm
    minimumSub (R e) sgm = sgm
    ret (E e) = e
    ret (R r) = r
    isR (E _) = False
    isR (R _) = True

normalizeByExtendedOrderedRewriting :: XOTRST -> [String] -> Term -> Term
normalizeByExtendedOrderedRewriting xotrst consts t
  | Just t0 <- anExtendedOrderedReduct xotrst consts t  = normalizeByExtendedOrderedRewriting xotrst consts t0
  | otherwise = t   




ex_orient :: ES -> [Precedence] -> XOTRS
ex_orient es precs = (nubBy isSameEquation es2, nubBy isSameRule trs2, precs)
  where (es2, trs2) = ex_orient1 es precs

ex_orient1 :: ES -> [Precedence] -> (ES, TRS)
ex_orient1 []            precs = ([], [])
ex_orient1 ((s, t) : es) precs
  | s == t                     = (es2, trs2)
  | ex_orientable precs (s, t) = (es2, (s, t) : trs2)
  | ex_orientable precs (t, s) = (es2, (t, s) : trs2)
  | otherwise                  = ((s, t) : es2, trs2)
  where
    (es2, trs2) = ex_orient1 es precs
