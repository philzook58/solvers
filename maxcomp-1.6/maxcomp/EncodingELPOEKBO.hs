module EncodingELPOEKBO where

import Data.List
import Term
import Rule
import TRS
import SMT
import qualified ELPO
import qualified EKBO
import qualified ELPOEKBO
import EncodingLinear
import Precedence hiding (gtPrec)

-- Encoding functions.

index :: TRS -> Rule -> Int
index trs rule
  | Just i <- elemIndex (Rule.rename "x" 1 rule) trs = i
  | otherwise = error "index"

varPrec :: String -> Exp
varPrec f = Var ("p_" ++ f)

gtPrec :: String -> String -> Formula
gtPrec f g = Gt (varPrec f) (varPrec g)

gtB :: Term -> Term -> Formula
gtB s@(F f _) t@(F g _)
  | f == g    = conj [labeled f, EncodingLinear.gtA (markTerm s) (markTerm t)]
  | otherwise = gtPrec f g
gtB _ _ = error "gtB"

geqB :: Term -> Term -> Formula
geqB s@(F f _) t@(F g _)
  | f == g    = 
    disj [neg (labeled f), 
          conj [labeled f, EncodingLinear.geqA (markTerm s) (markTerm t)]]
  | otherwise = bottom
geqB _ _ = error "geqB"

-- ELPO

varGtLPO :: TRS -> Term -> Term -> Formula
varGtLPO a s t = FVar ("gtLPO_" ++ show (index a (s, t)))

geqLPO :: TRS -> Term -> Term -> Formula
geqLPO a s t
  | s == t    = top
  | otherwise = varGtLPO a s t

gtLPO :: TRS -> Term -> Term -> Formula
gtLPO a s@(F _ _) t
  | elem s (subterms t) = bottom
  | otherwise           = disj [gtLPO1 a s t, gtLPO23 a s t]
gtLPO _ _         _ = bottom

gtLPO1 :: TRS -> Term -> Term -> Formula
gtLPO1 a (F _ ss) t = disj [ geqLPO a s t | s <- ss ]
gtLPO1 _ _        _ = bottom

gtLPO23 :: TRS -> Term -> Term -> Formula
gtLPO23 a s@(F _ ss) t@(F _ ts) =
  disj [conj (gtB s t : [ varGtLPO a s tj | tj <- ts ]),
        conj [geqB s t, lexGtLPO a s ss ts]]
gtLPO23 _ _ _ = bottom

lexGtLPO :: TRS -> Term -> [Term] -> [Term] -> Formula
lexGtLPO _ _ [] [] = Or []
lexGtLPO a u (s : ss) (t : ts)
  | s == t    = lexGtLPO a u ss ts
  | otherwise = conj (varGtLPO a s t : [ varGtLPO a u v | v <- ts ])
lexGtLPO _ _ _ _ = error "lexGtLPO"

varGtELPO :: TRS -> Term -> Term -> Formula
varGtELPO a s t = FVar ("gtELPO_" ++ show (index a (s, t)))

gtELPO :: TRS -> Term -> Term -> Formula
gtELPO a s t = conj [EncodingLinear.geqA s t, varGtLPO a s t]

encodeGtELPO :: TRS -> Term -> Term -> Formula
encodeGtELPO a s t = conj [EncodingLinear.geqA s t, varGtLPO a s t]

encodeELPO :: Signature -> TRS -> (Formula, [(Rule, Formula)])
encodeELPO sig trs =
  (conj (EncodingLinear.variableConstraint sig :
        Distinct [ varPrec f | (f, _) <- sig ] :
         [ implies (varGtLPO  a s t) (gtLPO  a s t) | (s, t) <- a ] ++
         [ implies (varGtELPO a s t) (gtELPO a s t) | (s, t) <- trs ]),
   [ ((l, r), varGtELPO a l r) | (l, r) <- trs ])
  where 
    a = nub [ Rule.rename "x" 1 (s, t) | (l, r) <- trs, s <- subterms l, t <- subterms r ]

-- EKBO

varW0 :: Exp
varW0 = Var "w0"

varWf :: String -> Exp
varWf f = Var ("wf" ++ f)

weight :: Term -> Exp
weight (V _)    = varW0
weight (F f ts) = Plus (varWf f : [ weight t | t <- ts ])

gtWeight :: Term -> Term -> Formula
gtWeight s t = Gt (weight s) (weight t)

geqWeight :: Term -> Term -> Formula
geqWeight s t = Geq (weight s) (weight t)

gtLex :: (Term -> Term -> Formula) -> [Term] -> [Term] -> Formula
gtLex _ [] [] = bottom
gtLex gt' (s : ss) (t : ts)
  | s == t    = gtLex gt' ss ts
  | otherwise = gt'   s t
gtLex _ _ _ = error "gtLex"

gtKBO :: Term -> Term -> Formula
gtKBO s t
  | elem s (subterms t) = bottom
  | nonduplicating (s, t) = 
      disj [gtWeight s t, 
            conj [geqWeight s t, gtKBO' s t]]
  | otherwise = bottom

gtKBO' :: Term -> Term -> Formula
gtKBO' s@(F f _) (V x)
  | EKBO.exponentialForm s f x = top
gtKBO' s@(F _ ss) t@(F _ ts) =
  disj [gtB s t,
        conj [geqB s t, gtLex gtKBO ss ts]]
gtKBO' _ _ = bottom

gtEKBO :: Term -> Term -> Formula
gtEKBO s t = conj [EncodingLinear.geqA s t, gtKBO s t] 

validityOfWeight :: Signature -> Formula
validityOfWeight sig =
  conj (Gt varW0 (Val 0) :
        [ Geq (varWf f) varW0   | (f, 0) <- sig ] ++
        [ Geq (varWf f) (Val 0) | (f, n) <- sig, n > 0 ])

admissibility1 :: Signature -> String -> Formula
admissibility1 sig f =
  disj [Gt (varWf f) (Val 0),
        conj (neg (labeled f) : [ gtPrec f g | (g, _) <- sig, f /= g ]) ]

admissibility :: Signature -> Formula
admissibility sig = 
  conj [ admissibility1 sig f | (f, 1) <- sig ] 

varGtEKBO :: TRS -> Term -> Term -> Formula
varGtEKBO a s t = FVar ("gtEKBO_" ++ show (index a (s, t)))

encodeEKBO :: Signature -> TRS -> (Formula, [(Rule, Formula)])
encodeEKBO sig trs =
  (conj (EncodingLinear.variableConstraint sig :
         [ implies (varGeqA a s t) (geqA s t) | (s, t) <- trs ] ++
         Distinct [ varPrec f | (f, _) <- sig ] :
         validityOfWeight sig :
         admissibility sig :
         [ implies (varGtKBO a l r) (gtKBO l r) | (l, r) <- trs ] ++
         [ implies (varGtEKBO a l r) (gtEKBO l r) | (l, r) <- trs ] ),
   [ ((l, r), varGtEKBO a l r) | (l, r) <- trs ])
  where 
    a = nub (TRS.rename "x" 1 trs)


-- ELPO + EKBO

varELPO :: Formula
varELPO = FVar "elpo"

varGt :: TRS -> Term -> Term -> Formula
varGt a s t = FVar ("gt_" ++ show (index a (s, t)))

varGeqA :: TRS -> Term -> Term -> Formula
varGeqA a s t = FVar ("geqA_" ++ show (index a (s, t)))

varGtKBO :: TRS -> Term -> Term -> Formula
varGtKBO a s t = FVar ("gtKBO_" ++ show (index a (s, t)))

gtELPOEKBO :: TRS -> Term -> Term -> Formula
gtELPOEKBO a s t
  | elem s (subterms t) = bottom
  | otherwise = 
      conj [varGeqA a s t,
            disj [conj [varELPO, varGtLPO a s t],
                  conj [neg varELPO, varGtKBO a s t]]]

encodeELPOEKBO :: Signature -> TRS -> (Formula, [(Rule, Formula)])
encodeELPOEKBO sig trs =
  (conj (EncodingLinear.variableConstraint sig :
        Distinct [ varPrec f | (f, _) <- sig ] :
         [ implies (varGeqA a s t) (geqA s t) | (s, t) <- trs ] ++
         [ implies (varGtLPO a s t) (gtLPO a s t) | (s, t) <- a ] ++
         implies (neg varELPO) (conj [validityOfWeight sig, admissibility sig]) :
         [ implies (varGtKBO a l r) (gtKBO l r) | (l, r) <- trs ] ++
         [ implies (varGt a l r) (gtELPOEKBO a l r) | (l, r) <- trs ]
        ),
   [ ((l, r), varGt a l r) | (l, r) <- trs ])
  where 
    a = nub [ Rule.rename "x" 1 (s, t) | (l, r) <- trs, s <- subterms l, t <- subterms r ]

-- Decoding functions.

decodeELPOEKBO :: Model -> Signature -> ELPOEKBO.Parameter
decodeELPOEKBO model sig
  | SMT.evalFormula model varELPO = ELPOEKBO.ELPO (decodeELPO model sig) 
  | otherwise                     = ELPOEKBO.EKBO (decodeEKBO model sig) 


-- Decoding functions.

decodePrecedence ::  Model -> Signature -> Precedence
decodePrecedence model sig = [ g | (g, _) <- sortOn (\(_, k) -> - k) a ]
  where a = [ (f, evalExp model (varPrec f)) | (f, _) <- sig ]

decodeELPO :: Model -> Signature -> ELPO.Parameter
decodeELPO model sig =
  (EncodingLinear.decode model sig,
   decodePrecedence model sig)

decodeWeight :: Model -> Signature -> EKBO.Weight
decodeWeight model sig =
  ([ (f, evalExp model (varWf f)) | (f, _) <- sig ],
   evalExp model varW0)

decodeEKBO :: Model -> Signature -> EKBO.Parameter
decodeEKBO model sig =
  (EncodingLinear.decode model sig,
   decodeWeight model sig,
   decodePrecedence model sig)
