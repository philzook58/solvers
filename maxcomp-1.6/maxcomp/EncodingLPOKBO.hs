module EncodingLPOKBO where

import Data.List
import Term
import Rule
import TRS
import SMT
import qualified KBO
import qualified EKBO
import Precedence hiding (gtPrec)

-- Encoding functions.

index :: TRS -> Rule -> Int
index []  _ = error "index"
index trs rule
  | Just i <- elemIndex (Rule.rename "x" 1 rule) trs = i
  | otherwise = error "index"

varPrec :: String -> Exp
varPrec f = Var ("p_" ++ f)

gtPrec :: String -> String -> Formula
gtPrec f g = Gt (varPrec f) (varPrec g)

-- LPO

varGtLPO :: TRS -> Term -> Term -> Formula
varGtLPO a s t = FVar ("gtLPO_" ++ show (index a (s, t)))

geqLPO :: TRS -> Term -> Term -> Formula
geqLPO a s t
  | s == t    = top
  | otherwise = varGtLPO a s t

gtLPO :: TRS -> Term -> Term -> Formula
gtLPO a s@(F _ _) t = disj [gtLPO1 a s t, gtLPO23 a s t]
gtLPO _ _         _ = bottom

gtLPO1 :: TRS -> Term -> Term -> Formula
gtLPO1 a (F _ ss) t = disj [ geqLPO a s t | s <- ss ]
gtLPO1 _ _        _ = bottom

gtLPO23 :: TRS -> Term -> Term -> Formula
gtLPO23 a s@(F f ss) (F g ts)
  | f == g    = lexGtLPO a s ss ts
  | otherwise = conj (gtPrec f g : [ varGtLPO a s tj | tj <- ts ])
gtLPO23 _ _ _ = bottom

lexGtLPO :: TRS -> Term -> [Term] -> [Term] -> Formula
lexGtLPO _ _ [] [] = Or []
lexGtLPO a u (s : ss) (t : ts)
  | s == t    = lexGtLPO a u ss ts
  | otherwise = conj (varGtLPO a s t : [ varGtLPO a u v | v <- ts ])
lexGtLPO _ _ _ _ = error "lexGtLPO"

encodeLPO :: Signature -> TRS -> (Formula, [(Rule, Formula)])
encodeLPO sig trs =
  (conj (Distinct [ varPrec f | (f, _) <- sig ] :
         [ implies (varGtLPO  a s t) (gtLPO  a s t) | (s, t) <- a ]),
   [ ((l, r), varGtLPO a l r) | (l, r) <- trs ])
  where 
    a = nub [ Rule.rename "x" 1 (s, t) | (l, r) <- trs, s <- subterms l, t <- subterms r ]

-- KBO

varW0 :: Exp
varW0 = Var "w0"

varWf :: String -> Exp
varWf f = Var ("wf_" ++ f)

weight :: Term -> Exp
weight (V _)    = varW0
weight (F f ts) = Plus (varWf f : [ weight t | t <- ts ])

gtWeight :: Term -> Term -> Formula
gtWeight s t = Gt (weight s) (weight t)

geqWeight :: Term -> Term -> Formula
geqWeight s t = Geq (weight s) (weight t)

gtKBO :: Term -> Term -> Formula
gtKBO s t
  | nonduplicating (s, t) = 
      disj [gtWeight s t, 
            conj [geqWeight s t, gtKBO' s t]]
  | otherwise = bottom

gtKBO' :: Term -> Term -> Formula
gtKBO' s@(F f _) (V x)
  | EKBO.exponentialForm s f x = top
gtKBO' (F f ss) (F g ts)
  | f == g    = lexGtKBO ss ts
  | otherwise = gtPrec f g
gtKBO' _ _ = bottom

lexGtKBO :: [Term] -> [Term] -> Formula
lexGtKBO [] [] = bottom
lexGtKBO (s : ss) (t : ts)
  | s == t    = lexGtKBO ss ts
  | otherwise = gtKBO s t
lexGtKBO _ _ = error "lexGtKBO"

validityOfWeight :: Signature -> Formula
validityOfWeight sig =
  conj (Gt varW0 (Val 0) :
        [ Geq (varWf f) varW0   | (f, 0) <- sig ] ++
        [ Geq (varWf f) (Val 0) | (f, n) <- sig, n > 0 ])

admissibility1 :: Signature -> String -> Formula
admissibility1 sig f =
  disj [Gt (varWf f) (Val 0),
        conj [ gtPrec f g | (g, _) <- sig, f /= g ] ]

admissibility :: Signature -> Formula
admissibility sig = 
  conj [ admissibility1 sig f | (f, 1) <- sig ] 

varGtKBO :: TRS -> Term -> Term -> Formula
varGtKBO a s t = FVar ("gtKBO_" ++ show (index a (s, t)))

encodeKBO :: Signature -> TRS -> (Formula, [(Rule, Formula)])
encodeKBO sig trs =
  (conj (Distinct [ varPrec f | (f, _) <- sig ] :
         validityOfWeight sig :
         admissibility sig :
         [ implies (varGtKBO a l r) (gtKBO l r) | (l, r) <- trs ]),
   [ ((l, r), varGtKBO a l r) | (l, r) <- trs ])
  where 
    a = nub (TRS.rename "x" 1 trs)

-- Decoding functions.

decodePrecedence ::  Model -> Signature -> Precedence
decodePrecedence model sig = [ g | (g, _) <- sortOn (\(_, k) -> - k) a ]
  where a = [ (f, evalExp model (varPrec f)) | (f, _) <- sig ]

decodeLPO :: Model -> Signature -> Precedence
decodeLPO model sig = decodePrecedence model sig

decodeWeight :: Model -> Signature -> KBO.Weight
decodeWeight model sig =
  ([ (f, evalExp model (varWf f)) | (f, _) <- sig ],
   evalExp model varW0)

decodeKBO :: Model -> Signature -> KBO.Parameter
decodeKBO model sig =
  (decodeWeight model sig,
   decodePrecedence model sig)
