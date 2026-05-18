module AC where

-- implements Theorem 5.1. of Avenhaus et al. (2003)
-- see also https://github.com/nick8325/twee/commit/f63ee2411432ab52dec064b2dd3c7f5ef6454189

import Data.IntSet as IS
import Data.Maybe

import Proof
import Rewriting
import Rule
import Term
import ReductionOrder

-- HACK: function symbols are non-negative
skolemize :: Term -> Term
skolemize (V x) = F (- (x + 1)) []
skolemize (F f ts) = F f [ skolemize t | t <- ts ]

-- used for "sorting" terms modulo AC 
-- assumes skolemization
gtLPO :: Term -> Term -> Bool
gtLPO t@(F f ts) u@(F g us) =
  any (\ti -> ti == u || gtLPO ti u) ts ||
  (all (\uj -> gtLPO t uj) us &&
    (f > g || (f == g && lex' ts us)) )
  where
    lex' [] [] = False
    lex' (ti : ts') (ui : us')
      | ti == ui = lex' ts' us'
      | otherwise = gtLPO ti ui
    lex' _ _ = False
gtLPO _ _ = error "gtLPO assumes skolemized terms (bug)"

aof :: (Term, Term) -> Maybe Int
aof (F f1 [ F f2 [ V x, V y ], V z], F f3 [ V x', F f4 [ V y', V z' ]])
  | all (\fi -> f1 == fi) [f2, f3, f4] && x == x' && y == y' && z == z'
    = return f1
aof (F f1 [ V x, F f2 [ V y, V z ]], F f3 [ F f4 [ V x', V y' ], V z' ])
  | all (\fi -> f1 == fi) [f2, f3, f4] && x == x' && y == y' && z == z'
    = return f1
aof _ = Nothing

isa :: (Term, Term) -> Bool
isa = isJust . aof

cof :: (Term, Term) -> Maybe Int
cof (F f1 [ V x, V y ], F f2 [ V y', V x' ])
  | f1 == f2 && x == x' && y == y' = return f1
cof _ = Nothing

isc :: (Term, Term) -> Bool
isc = isJust . cof

acSymbols :: [(Term, Term)] -> (IS.IntSet, IS.IntSet) 
acSymbols es = acs' es (IS.empty) (IS.empty)
  where
    acs' [] as cs = (as, cs)
    acs' ((s, t) : rest) as cs =
      let as' = case aof (s, t) of Just f -> IS.insert f as; _ -> as
          cs' = case cof (s, t) of Just f -> IS.insert f cs; _ -> cs 
      in acs' rest as' cs'

redundant' :: IS.IntSet -> IS.IntSet -> (Term, Term) -> Bool
redundant' as cs (s, t) =
  not (isc (s, t)) && not (isa (s, t)) && not (isPerm (s, t)) &&
  normalize (skolemize s) == normalize (skolemize t)
  where
    isPerm (F f1 [ V x, F f2 [ V y, V z ]], F f3 [ V y', F f4 [ V x', V z' ]])
      = f1 == f2 && f1 == f3 && f1 == f4 && x == x' && y == y' && z == z'
    isPerm _ = False
    a f = Rule {
      _id = 0, -- don't care
      _lhs = F f [ F f [ V 0, V 1], V 2 ],
      _rhs = F f [ V 0, F f [ V 1, V 2 ]],
      _orientation = Oriented,
      _depth = 0, -- don't care
      _proof = Axiom Nothing
    }
    c f = Rule {
      _id = 0, -- don't care
      _lhs = F f [ V 0, V 1 ],
      _rhs = F f [ V 1, V 0 ],
      _orientation = Unoriented,
      _depth = 0, -- don't care
      _proof = Axiom Nothing
    }
    p f = Rule {
      _id = 0, -- don't care
      _lhs = F f [ V 0, F f [ V 1, V 2]],
      _rhs = F f [ V 1, F f [ V 0, V 2]],
      _orientation = Unoriented,
      _depth = 0, -- don't care
      _proof = Axiom Nothing
    }
    acrules = concat [ [a f, c f, p f] | f <- IS.toList (IS.intersection as cs) ]
    crules = [ c f | f <- IS.toList (IS.difference cs as) ]
    normalize :: Term -> Term
    normalize u = fst (nf gtLPO (acrules ++ crules) u)

redundant :: ReductionOrder -> IS.IntSet -> IS.IntSet -> (Term, Term) -> Bool
redundant (KBO _) as cs (s, t) = redundant' as cs (s, t)
redundant (LPO _) as cs (s, t) = redundant' as cs (s, t)
redundant _ _ _ _ = False -- for other classes, for example (X + Y) + Z > X + (Y + Z) is not guaranteed!
