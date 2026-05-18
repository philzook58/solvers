module Connectedness where

-- implements connectedness based on 3.2 of Smallbone (2021)

import qualified Data.IntMap as IM

import Signature
import Rewriting
import qualified RewritingIndexing as RI
import Rule
import Term
import ReductionOrder
import qualified KBO
import qualified LPO

-- whether t = u is connected below s
-- assumes s > t and s > u
connected :: ReductionOrder -> Signature -> IM.IntMap Rule -> RI.Index -> RI.Index -> Term -> Term -> Term -> Bool
connected to sig rules oriented_idx unoriented_idx t s u = connected' to
  where
    connected' (KBO p) =
      let gt1 t1 t2 = gt to s t2 && KBO.gtSk m1 p t1 t2
          gt2 t1 t2 = gt to s t2 && KBO.gtSk m2 p t1 t2
      in normalize gt1 t == normalize gt1 u || normalize gt2 t == normalize gt2 u
    connected' (LPO p) =
      let gt1 t1 t2 = gt to s t2 && LPO.gtSk m1 p t1 t2
          gt2 t1 t2 = gt to s t2 && LPO.gtSk m2 p t1 t2
      in normalize gt1 t == normalize gt1 u || normalize gt2 t == normalize gt2 u
    connected' _ = False -- TODO: support WPO and MSPO?
    normalize rel v =
      fst (nfWithIndex sig rel rules oriented_idx unoriented_idx v)
    vs = variables_ordered [t, u]
    m1 = IM.fromList (zip vs [0..])
    m2 = IM.fromList (zip (reverse vs) [0..])
