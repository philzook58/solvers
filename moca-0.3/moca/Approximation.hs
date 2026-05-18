module Approximation where

import Data.List
import Data.Ord

import Terms
import Substitutions
import Rules
import Trie
import Lists
import OrderedRewriting
import LPOTerminationCheck
import Debug.Trace
import Parameters

type Projection = (String, Int)
-- e.g., when f has arity 3, then ("f", 1) represents the rule f(x, y, z) -> y.

approximations :: Parameter -> OTRST -> [(OTRS, [Projection])]
approximations prm otrst@(otrs, _) = projections ++ generalizations
  where projections
          | noApproximationsByProjection prm    = []
          | otherwise                           = [collapsingExtension otrs [], unaryProjection otrs]
        generalizations 
          | noApproximationsByGenalization prm  = []
          | otherwise                           = [(cap 1 otrst, [])]

-- cap
cap :: Int -> OTRST -> OTRS
cap k ((es, trs, prec), trie) = orient (capES k (es ++ trs) prec) prec

capES :: Int -> ES -> Precedence -> ES
capES k es prec = [ capEquation k prec es2 e | e <- es1 ] 
  where
    es1 = renameES "X" es 
    es2 = renameES "Y" es

capEquation :: Int -> Precedence -> ES -> Equation -> Equation
capEquation k prec es e@(s, t) = replaceEquationInParallel e plrvs
  where
    sps s0 t0 lr = nub [ (s', (p, lr))
                        | p <- functionPositions s0, p /= [],
                          s' <- [subtermAt s0 p], vars s' /= [],
                          (u, v) <- es ++ inverse es,
                          Just sigma <- [mgu s' u], -- TODO Trie?
                          unorientable prec (substituteEquation (t0, s0) sigma) &&
                          unorientable prec (substituteEquation (v, u) sigma) ]
    plrvs = [ (plr, V ("Z" ++ show i))
            | (plrs, i) <- zip (grouping (sps s t "L" ++ sps t s "R") ) [1..],
              length plrs >= k,
              plr <- plrs ]
    {- memo:
      if    s = h(a(f(X1, X2)), g(X2), f(X1,X2)), 
            sps = [(f(X1, X2), 11), (g(X2), 2), (f(X1, X2), 3)], and k = 1,
      then  (zip (grouping sps) [1..]) = [([11, 3], 1), ([2], 2)],
            pvs = [(11, Z1), (3, Z1), (2, Z2)]
    -}

-- unaryProjection
unaryProjection :: OTRS -> (OTRS, [Projection])
unaryProjection (es, trs, prec) = (orient (projectES fis (es ++ trs)) prec, fis)
  where fis = nub [ (f, 0) | (s, t) <- es ++ trs, F f [_] <- [s, t] ]

-- collapsing extension (collapsing OTRS using rules like f(c, x, h(c)) -> x)
collapsingExtension :: OTRS -> [Projection] -> (OTRS, [Projection])
collapsingExtension otrs fis | identicalOTRS otrs otrs'  = (otrs, fis)
                             | otherwise                 = collapsingExtension otrs' fis'
  where (otrs', fis') = collapsingExtension1 otrs fis
collapsingExtension1 :: OTRS -> [Projection]  -> (OTRS, [Projection])
collapsingExtension1 (es, trs, prec) fis0 = (orient (projectES fis (es ++ trs)) prec, fis0 ++ fis)
  where fis = filterOut [ (f, i) | (F f ls, V x) <- es',
                                   Just i <- [elemIndex (V x) ls],
                                   not (occursInSomeTerm x (removeAt i ls)) ]
        es' = nubBy isSameRule (es ++ inverse es ++ trs)
{-
  memo: if there exists f(g(y), x, g(c), c) -> x,
  then ("f", 1) is appended to fis
  if there also exists f(g(y), c, x, c) -> x,
  then ("f", 2) (or ("f", 1) ) is ignored by "filterOut"
-}

remarkForCollapsing :: [Projection] -> String
remarkForCollapsing [] = ""
remarkForCollapsing fis = "with the following interpretations:" ++ "\n\t" ++ 
                          intercalate "\n\t" [ f ++ " returns " ++ show (i + 1) ++ th (i + 1) ++ " variable" | (f, i) <- fis ]
  where th 1 = "st"
        th 2 = "nd"
        th 3 = "rd"
        th _ = "th"
                            



divergenceCritic :: ES -> ES
divergenceCritic es 
  = nubBy isSameEquation
      (removeTrivialEquations
        [ (replace l2 (V newV) (p1 ++ p2), replace r2 (replace l2 (V newV) p1) q2)
        | e1@(l1, r1) <- symmetric es, e2@(l2, r2) <- symmetric es, e3@(l3, r3) <- symmetric es, 
          not (isSameEquation e1 e2),  not (isSameEquation e1 e3),  not (isSameEquation e2 e3),
          p1 <- allPositions l1, 
          p1 `elem` allPositions l2,
          p2 <- allPositions (subtermAt l2 p1), 
          (p1 ++ p2 ++ p2) `elem` allPositions l3,
          q2 <- allPositions r2,
          (q2 ++ q2) `elem` allPositions r3,
          variant 
            (F "" [l1, r1] ) 
            (F "" [replace l2 (subtermAt l2 (p1 ++ p2)) p1, subtermAt r2 q2] ),
          variant 
            (F "" [l2, l2, r2, r2] ) 
            (F "" [replace l3 (subtermAt l3 (p1 ++ p2 ++ p2)) (p1 ++ p2), 
                   replace l3 (subtermAt l3 (p1 ++ p2)) p1, 
                   replace r3 (subtermAt r3 (q2 ++ q2)) q2, 
                   subtermAt r3 q2] )
        ] 
      )
  where newV = freshVariableName (freshVariableSymbolNumber es)
{-
  memo: { f(s(0)) = c, f(s(s(0)) = c, f(s(s(s(0)))) = c } will generate f(s(x)) = c
-}
