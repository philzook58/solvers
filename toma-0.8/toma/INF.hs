{-# LANGUAGE OverloadedStrings #-}
module INF where

import Data.Text ()
import qualified Data.Set as S
import Data.List

import Parsing

type CRule = ((Term, Term), [(Term, Term)]) -- conditional rule
type Query = (Term, Term)

signatureOf'' :: [CRule] -> [Query] -> Signature
signatureOf'' rules qs = signatureOf (ts1 ++ ts2)
  where
    unfold (l, r) = [l, r] 
    ts1 = [ t | (e, cs) <- rules, t <- concatMap unfold (e : cs) ]
    ts2 = concatMap unfold qs

liftGoal :: [CRule] -> [Query] -> ([CRule], Query)
liftGoal rules qs = (qrule : rules, (true, false))
  where
    sig = signatureOf'' rules qs
    true = F (fresh sig "true") []
    false = F (fresh sig "false") []
    qrule = ((true, false), qs)

project :: [CRule] -> [(Term, Term)]
project crules = [ (l, r) | ((l, r), _) <- crules ]

-- Marchiori's unraveling
-- see Definition 7.2.11 of Ohlebusch's book
-- this is enough for 1-CTRS, but can be improved for {2, 3}-CTRS?
unravel :: Signature -> [CRule] -> [(Term, Term)]
unravel sig crules = map fst nonconditionals ++ recur (freshes sig "u") (group' conditionals)
  where
    (nonconditionals, conditionals) = partition (\(_, cs) -> null cs) crules
    unravel' u ((l, r), cs) =
      let ss = map fst cs
          ts = map snd cs 
          extra = [ V v | v <- S.toList (variables l) ] -- TODO: better choice?
          rule1 = (l, F u (ss ++ extra))
          rule2 = (F u (ts ++ extra), r)
      in [rule1, rule2]
    similar ((l1, _), cs1) ((l2, _), cs2) =
      variant (F "" (l1 : map fst cs1)) (F "" (l2 : map fst cs2))
    group' [] = []
    group' (e : es) =
      case partition (similar e) es of
        (similars, others) -> (e : similars) : group' others
    recur _ [] = []
    recur us (g : rest) = concat [ unravel' (head us) rule | rule <- g ]  ++ recur (tail us) rest

-- reduction to word problem
transform :: [CRule] -> [Query] -> ([(Term, Term)], Query)
transform crules qs = (unravel sig crules', q)
  where
    (crules', q) = liftGoal crules qs
    sig = signatureOf'' crules [q]
