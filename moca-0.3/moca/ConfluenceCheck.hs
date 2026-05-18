module ConfluenceCheck where

import Lists
import Terms
import Substitutions
import Rules
import FingerPrint
import Trie
import OrderedRewriting
import Data.List
import Data.Ord
import Debug.Trace

import LPOTerminationCheck


-- naive way (using trie)
ecp :: OTRST -> [TermPair]
ecp (o@(es, trs, prec), trie) = [ neq | er <- sortERs (mixOfESAndTRS (symmetric es) trs), neq <- ecp1 er (o, trie) ]
ecp1 :: EquationOrRule -> OTRST -> [TermPair]
ecp1 er0 ((es, trs, prec), trie)
  = [ (substitute (replace l2 r1 p) sgm, substitute r2 sgm)
    | let (l1 ,r1) = ret er0,
      (l2, r2) <- [ ret er | er <- getUnifiableRules trie l1 ],
      p <- allPositions l2,
      F _ _ <- [subtermAt l2 p],
      Just sgm <- [mgu l1 (subtermAt l2 p)],
      (unorientable prec (substitute r1 sgm, substitute l1 sgm) ),
      (unorientable prec (substitute r2 sgm, substitute l2 sgm) ) ]
  where 
    ret (E e) = e
    ret (R r) = r
    isR (E _) = False 
    isR (R _) = True

-- slanting search
ecp_preSorted :: OTRST -> [TermPair]
ecp_preSorted ((es, trs, prec), trie) = [ ecpair | ecpairs <- ecpairss, ecpair <- ecpairs ]  
  where ecpairss =  [ extendedCriticalPairs prec er1 er2 
                    | (er1, er2) <- pairsSlanting (sortERs (mixOfESAndTRS (symmetric es) trs))]



extendedCriticalPairs :: Precedence -> EquationOrRule -> EquationOrRule -> [TermPair]
extendedCriticalPairs prec er1 er2 = [ (s, t) | (s, _, t) <- extendedCriticalPeaks prec er1 er2 ]
  
-- find all extended critical pairs of two rules
extendedCriticalPeaks :: Precedence -> EquationOrRule -> EquationOrRule -> [(Term, Term, Term)]
extendedCriticalPeaks prec er1 er2 = ecpeaks (rnm "X" er1) (rnm "Y" er2)
  where 
    rnm str (E e0) = E (renameEquation str e0)
    rnm str (R r0) = R (renameEquation str r0)
    ret (E e) = e
    ret (R r) = r
    ecpeaks er1' er2' = [ (substitute (replace l2 r1 p) sgm, substitute l2 sgm, substitute r2 sgm)
                        | (l1, r1) <- [ret er1'], (l2, r2) <- [ret er2'],
                          p <- allPositions l2,
                          F _ _ <- [subtermAt l2 p],
                          Just sgm <- [mgu l1 (subtermAt l2 p)],
                          ( isR er1' || unorientable prec (substitute r1 sgm, substitute l1 sgm) ),
                          ( isR er2' || unorientable prec (substitute r2 sgm, substitute l2 sgm) ) ]
    isR (E _) = False 
    isR (R _) = True

extendedCriticalPairs2 :: Precedence -> EquationOrRule -> EquationOrRule -> [TermPair]
extendedCriticalPairs2 prec er1 er2 = [ (s, t) | (s, _, t) <- extendedCriticalPeaks2 prec er1 er2 ]
-- find all extended critical pairs of two rules
extendedCriticalPeaks2 :: Precedence -> EquationOrRule -> EquationOrRule -> [(Term, Term, Term)]
extendedCriticalPeaks2 prec er1 er2 = ecpeaks (rnm "X" er1) (rnm "Y" er2)
  where 
    rnm str (E e0) = E (renameEquation str e0)
    rnm str (R r0) = R (renameEquation str r0)
    ret (E e) = e
    ret (R r) = r
    ecpeaks er1' er2' = [ (substitute (replace l2 r1 p) sgm, substitute l2 sgm, substitute r2 sgm)
                        | (l1, r1) <- [ret er1'], (l2, r2) <- [ret er2'],
                          p <- allPositions l2,
                          F _ _ <- [subtermAt l2 p],
                          Just sgm <- [mgu l1 (subtermAt l2 p)]]
    isR (E _) = False 
    isR (R _) = True

nonGroundJoinableECPs :: OTRST -> [String] -> [(Term, Term)]
nonGroundJoinableECPs otrst consts 
  = nubBy isSameEquation [ (nf' s, nf' t)
                          | (s, t) <- nubBy isSameEquation (ecp_preSorted otrst),
                            not (groundJoinable otrst consts (nf' s) (nf' t)) ]
  where nf' s0 = OrderedRewriting.normalize otrst consts s0

groundJoinable :: OTRST -> [String] -> Term -> Term -> Bool
groundJoinable otrst consts s t  
  | OrderedRewriting.join otrst consts s t  = True  
  | instanceOf otrst s t                    = True
  | groundJoinable_C otrst consts s t       = True
groundJoinable otrst consts (F f ss) (F g ts)  
  | f == g                                  = and [ groundJoinable otrst consts s' t' 
                                                  | (s', t') <- zip ss ts ]
groundJoinable otrst consts s t             = False

groundJoinable_C :: OTRST -> [String] -> Term -> Term -> Bool
groundJoinable_C otrst@((es, trs, prec), trie) consts s t
  = and [ nf' qprec s == nf' qprec t | qprec <- partitionsWithOrders (varsInEquation (s,t)) ]
  where nf' qprec0 s0 = normalizeByExtendedOrderedRewriting ((es, trs, [prec, qp2p qprec0]), trie) consts (v2c qprec0 s0) 
        v2c qp0 (V x)    = F x0 []                        where x0 : _ = [ y | xs@(y:ys) <- qp0, x `elem` xs ]
        v2c qp0 (F f ts) = F  f [ v2c qp0 t | t <- ts ]
        qp2p qp0 = [ y | y : ys <- qp0 ]
-- Note: trie does not depend on reduction order.

instanceOf :: OTRST -> Term -> Term -> Bool--TODO trie?
instanceOf ((es, trs, _), trie) s t 
  = or [ match (F "" [s', t']) (F "" [s, t]) /= Nothing 
       | (s', t') <- symmetric es ++ trs ]





