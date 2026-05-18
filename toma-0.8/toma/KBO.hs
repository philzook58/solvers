{-# LANGUAGE OverloadedStrings #-}
module KBO where

import qualified Data.Vector as V
import qualified Data.IntSet as IS
import qualified Data.IntMap as IM
import qualified Data.Text as T

import Term
import qualified Precedence as Pr
import qualified Weight as W
import Signature

type Param = (W.Weight, Pr.Precedence)

pp :: Signature -> Param -> T.Text
pp sig (w, pr) = "KBO with weight " <> W.pp sig w <> " and precedence " <> Pr.pp sig pr

-- weight (w0, w) and precedence > is admissible if
-- if w(f) = 0 for a unary function symbol then f > g for all other function symbols g.
-- quasi-precedence is not supported.
admissible :: Signature -> Param -> Bool
admissible sig ((_, w'), pr) =
  case [ f | f <- unaries sig, w' V.! f == 0 ] of
    [] -> True
    [f] -> all id [ Pr.gt pr f g  | (g, _) <- V.toList (V.indexed sig) ]
    _ -> False

-- smart constructor which checks validity and admissibility
param :: Signature -> W.Weight -> Pr.Precedence -> Param
param sig w pr
  | W.valid sig w && admissible sig (w, pr) = (w, pr)
  | not (W.valid sig w) = error (T.unpack ("param: invalid weight " <> W.pp sig w))
  | not (admissible sig (w, pr)) = error (T.unpack ("param: admissibility violation in " <> KBO.pp sig (w, pr)))
  | otherwise = error "param: unreachable"

-- Twee's default KBO
frequencyAsc, frequencyDesc :: Signature -> [Term] -> Param
frequencyAsc sig ts = param sig (W.defaultWeight sig) (Pr.frequencyAsc sig ts)
frequencyDesc sig ts = param sig (W.defaultWeight sig) (Pr.frequencyDesc sig ts)

-- NOTE: quasi-precedence is not supported
gt :: Param -> Term -> Term -> Bool
gt _ (V _) _ = False
gt _ s@(F _ _) (V x) = IS.member x (Term.variables s)
gt (w, pr) s@(F f ss) t@(F g ts) =
  nonDuplicating (s, t) && (ws > wt || (ws >= wt && (Pr.gt pr f g || (f == g && gtlex ss ts))))
  where
    ws = W.weight w s
    wt = W.weight w t
    gtlex [] _ = False
    gtlex (_ : _) [] = True
    gtlex (s' : ss') (t' : ts') = gt (w, pr) s' t' || (s' == t' && gtlex ss' ts')

-- skolemized KBO
-- IntMap specifies ordering between variables
-- variables are assumed to be smallest
gtSk :: IM.IntMap Int -> Param -> Term -> Term -> Bool
gtSk m _ (V x) (V y)
  | Just px <- IM.lookup x m, Just py <- IM.lookup y m = px > py
  | otherwise = False -- NOTE: unoriented equation like f(X) = g(Y) could be applied in connectedness
gtSk _ _ (V _) (F _ _) = False
gtSk _ _ (F _ _) (V _) = True
gtSk m (w, pr) s@(F f ss) t@(F g ts) =
  nonDuplicating (s, t) && (ws > wt || (ws >= wt && (Pr.gt pr f g || (f == g && gtlex ss ts))))
  where
    ws = W.weight w s
    wt = W.weight w t
    gtlex [] _ = False
    gtlex (_ : _) [] = True
    gtlex (s' : ss') (t' : ts') = gtSk m (w, pr) s' t' || (s' == t' && gtlex ss' ts')
