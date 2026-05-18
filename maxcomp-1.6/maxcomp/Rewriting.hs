module Rewriting where

import Term
import Rule
import TRS

data MarkedTerm =
    NF Term
  | Active String [MarkedTerm]

substitute :: Term -> Subst -> MarkedTerm
substitute t@(V _)    sigma = NF (Term.substitute t sigma)
substitute (F f ts) sigma =
  Active f [ Rewriting.substitute t sigma | t <- ts ]

-- innermost rewriting

rewriteAtRoot :: TRS -> Term -> MarkedTerm
rewriteAtRoot [] t = NF t
rewriteAtRoot ((l, r) : trs) t
  | Just sigma <- match l t = Rewriting.substitute r sigma
  | otherwise = rewriteAtRoot trs t

nf' :: TRS -> MarkedTerm -> Term
nf' _   (NF s)        = s
nf' trs (Active f ss) = 
  nf' trs (rewriteAtRoot trs (F f [ nf' trs s | s <- ss ]))

activate :: Term -> MarkedTerm
activate t@(V _)  = NF t
activate (F f ts) = Active f [ activate t | t <- ts ]

nf :: TRS -> Term -> Term
nf trs t = nf' trs (activate t)

nfEq :: TRS -> Rule -> Rule
nfEq trs (s, t) = (nf trs s, nf trs t)

normalizeES :: TRS -> TRS -> TRS
normalizeES trs es =
  [ (s, t) | e <- es, let (s, t) = nfEq trs e, s /= t ]
