module Rule where

import Data.List
import Term

type Rule = (Term, Term)

showRule :: Rule -> String
showRule (l, r) = show l ++ " -> " ++ show r

-- Var(l -> r) = Var(l) cup Var(r)
variables :: Rule -> [String]
variables (l, r) = union (Term.variables l) (Term.variables r)

-- Fun(l -> r) = Fun(l) cup Fun(r)
functions :: Rule -> [String]
functions (l, r) = union (Term.functions l) (Term.functions r)

signatureOf :: Rule -> Signature
signatureOf (l, r) = union (Term.signatureOf l) (Term.signatureOf r) 

-- |l -> r| = |l| + |r|
size :: Rule -> Int
size (l, r) = Term.size l + Term.size r

substitute :: Rule -> Subst -> Rule
substitute (l, r) sigma =
  (Term.substitute l sigma, Term.substitute r sigma)

rename :: String -> Int -> Rule -> Rule
rename x k (l, r) = (Term.substitute l sigma, Term.substitute r sigma)
  where
    ys = union (Term.variables l) (Term.variables r)
    sigma = [ (y, V (x ++ show i)) | (y, i) <- zip ys [k :: Int ..] ]

subsume :: Rule -> Rule -> Bool
subsume (l1, r1) (l2, r2) = Term.subsume (F "" [l1,r1]) (F "" [l2,r2]) 

variant :: Rule -> Rule -> Bool
variant rule1 rule2 =
  Rule.subsume rule1 rule2 &&
  Rule.subsume rule2 rule1

variantEq :: Rule -> Rule -> Bool
variantEq (s, t) e =
  Rule.variant (s, t) e ||
  Rule.variant (t, s) e


subset :: Eq a => [a] -> [a] -> Bool
subset xs ys = all (\x -> elem x ys) xs

extraVariables :: Rule -> [String]
extraVariables (l, r) =
  nub [ x | x <- Term.variables r, not (elem x (Term.variables l)) ]

variableCondition :: Rule -> Bool
variableCondition (V _, _) = False
variableCondition (l, r)   = subset (Term.variables r) (Term.variables l)

nonduplicating :: Rule -> Bool
nonduplicating (l, r) = all p (Term.variables r)
  where p x = count l x >= count r x

strictlyLengthReducing :: Rule -> Bool
strictlyLengthReducing (l, r) =
  Term.size l > Term.size r && nonduplicating (l, r)

collapsing :: Rule -> Bool
collapsing (_, V _) = True
collapsing _        = False