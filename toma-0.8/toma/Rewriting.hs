module Rewriting (nf, nfWithIndex) where

import qualified Data.IntSet as IS
import qualified Data.IntMap.Strict as IM

import Term
import Rule
import qualified RewritingIndexing as RI
import Signature

-- implementation of ordered innermost rewriting

-- lighter version of rewriting (e.g., full superdevelopment)
-- might be useful for partial inter-reduction

-- term with marking (nf or not)
-- variables are always nf
data Marked = MF Int [Marked] | NF Term

mark :: Term -> Marked
mark t@(V _) = NF t
mark (F f ts) = MF f [ mark t | t <- ts ]

-- assumes σ(x) is NF for all x
substitute :: Term -> Subst -> Marked
substitute (V x) sigma =
  case IM.lookup x sigma of 
    Just t -> NF t
    Nothing -> NF (V x)
substitute (F f ts) sigma =
  MF f [ Rewriting.substitute t sigma | t <- ts ]

-- returns (t, X) if s -ε-> t by rule X in the TRS 
rewriteAtRoot :: (Term -> Term -> Bool) -> [Rule] -> Term -> Maybe (Marked, Int)
rewriteAtRoot _ [] _ = Nothing
rewriteAtRoot gt (rule : rest) t
  | oriented rule =
      case match (_lhs rule) t of
        Just sigma -> return (Rewriting.substitute (_rhs rule) sigma, _id rule)
        Nothing -> rewriteAtRoot gt rest t
  | Just sigma <- match (_lhs rule) t, gt (tsub (_lhs rule) sigma) (tsub (_rhs rule) sigma) =
      return (Rewriting.substitute (_rhs rule) sigma, _id rule)
  | Just sigma <- match (_rhs rule) t, gt (tsub (_rhs rule) sigma) (tsub (_lhs rule) sigma) =
      return (Rewriting.substitute (_lhs rule) sigma, _id rule)
  | otherwise = rewriteAtRoot gt rest t
  where
    tsub u sigma = Term.substitute u sigma

rewriteAtRoot' :: (Term -> Term -> Bool) -> IM.IntMap Rule -> [Either Int Int] -> Term -> Maybe (Marked, Int)
rewriteAtRoot' gt rules matches t = loop matches
  where
    tsub u sigma = Term.substitute u sigma
    rsub u sigma = Rewriting.substitute u sigma
    getRule i = rules IM.! i
    loop [] = Nothing
    loop (Left i : rest) = 
      case match (_lhs rule) t of
        Just sigma
          | oriented rule -> return (rsub (_rhs rule) sigma, i)
          | gt (tsub (_lhs rule) sigma) (tsub (_rhs rule) sigma) -> return (rsub (_rhs rule) sigma, i)
          | otherwise -> loop rest
        Nothing -> loop rest
      where
        rule = getRule i
    loop (Right i : rest) =
      case match (_rhs rule) t of
        Just sigma
          | oriented rule -> error "rewriteAtRoot': oriented rules must be ordered from left to right (bug)"
          | gt (tsub (_rhs rule) sigma) (tsub (_lhs rule) sigma) -> return (rsub (_lhs rule) sigma, i)
          | otherwise -> loop rest
        Nothing -> loop rest  
      where
        rule = getRule i

-- TODO: tail recursive version?
nf :: (Term -> Term -> Bool) -> [Rule] -> Term -> (Term, IS.IntSet)
nf gt trs t = nf' (mark t)
  where
    nf' (NF u) = (u, IS.empty)
    nf' (MF f us) =
      case rewriteAtRoot gt trs (F f us') of
        Just (u', i) ->
          let (u'', s'') = nf' u'
            in (u'', IS.insert i (IS.union s' s''))
        Nothing -> (F f us', s')
      where
        nfs = [ nf' u | u <- us ]
        us' = [ u | (u, _) <- nfs ]
        s' = IS.unions ([ s'' | (_, s'') <- nfs ])

nfWithIndex :: Signature -> (Term -> Term -> Bool) -> IM.IntMap Rule -> RI.Index -> RI.Index -> Term -> (Term, IS.IntSet)
nfWithIndex sig gt rules oind uoind t = nf' (mark t)
  where
    nf' (NF u) = (u, IS.empty)
    nf' (MF f us) =
      case rewriteAtRoot' gt rules (RI.retrieve sig fus' oind ++ RI.retrieve sig fus' uoind) fus' of
        Just (u', i) ->
          let (u'', s'') = nf' u'
            in (u'', IS.insert i (IS.union s' s''))
        Nothing -> (F f us', s')
      where
        nfs = [ nf' u | u <- us ]
        us' = [ u | (u, _) <- nfs ]
        fus' = F f us' -- term with normalized arguments
        s' = IS.unions ([ s'' | (_, s'') <- nfs ])
