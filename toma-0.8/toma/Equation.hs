module Equation where

import Term

-- subsumption check of *directed* rules
subsumes :: (Term, Term) -> (Term, Term) -> Bool
(l1, r1) `subsumes` (l2, r2) = Term.subsumes t1 t2
  where
    t1 = F (-1) [l1, r1]
    t2 = F (-1) [l2, r2]

-- variant check of *directed* rules
-- HACK: -1 is not used as a function symbol
variant :: (Term, Term) -> (Term, Term) -> Bool
variant e1 e2 = Equation.subsumes e1 e2 && Equation.subsumes e2 e1
