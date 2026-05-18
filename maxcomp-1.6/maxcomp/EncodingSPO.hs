module EncodingSPO where

import Data.List
import Term
import Rule
import TRS
import SMT
import qualified SPO
import EncodingLinear2
import Precedence

-- Encoding functions.

index :: TRS -> Rule -> Int
index []  _ = error "index"
index trs rule
  | Just i <- elemIndex (Rule.rename "x" 1 rule) trs = i
  | otherwise = error "index"

varPrec :: String -> Exp
varPrec f = Var ("p_" ++ f)

encodeGtPrec :: String -> String -> Formula
encodeGtPrec f g = Gt (varPrec f) (varPrec g)

encodeGeqSq :: Term -> Term -> Formula
encodeGeqSq s@(F f _) t@(F g _) =
  disj [ 
    encodeGtA 1 (markTerm s) (markTerm t),
    conj [encodeGeqA 1 (markTerm s) (markTerm t), encodeGtA 2 (markTerm s) (markTerm t)],
    conj [encodeGeqA 1 (markTerm s) (markTerm t), encodeGeqA 2 (markTerm s) (markTerm t), if f == g then top else encodeGtPrec f g]
  ]
encodeGeqSq s t
  | s == t = top
  | otherwise = bottom

encodeGtSq :: Term -> Term -> Formula
encodeGtSq s@(F f _) t@(F g _) =
  disj [ 
    encodeGtA 1 (markTerm s) (markTerm t),
    conj [encodeGeqA 1 (markTerm s) (markTerm t), encodeGtA 2 (markTerm s) (markTerm t)],
    conj [encodeGeqA 1 (markTerm s) (markTerm t), encodeGeqA 2 (markTerm s) (markTerm t), encodeGtPrec f g ]
  ]
encodeGtSq _ _ = bottom

-- SPO

varGtSPO :: TRS -> Term -> Term -> Formula
varGtSPO a s t = FVar ("gtSPO_" ++ show (index a (s, t)))

geqSPO :: TRS -> Term -> Term -> Formula
geqSPO a s t
  | s == t    = top
  | otherwise = varGtSPO a s t

gtSPO :: TRS -> Term -> Term -> Formula
gtSPO a s@(F _ _) t = disj [gtSPO1 a s t, gtSPO23 a s t]
gtSPO _ _         _ = bottom

gtSPO1 :: TRS -> Term -> Term -> Formula
gtSPO1 a (F _ ss) t = disj [ geqSPO a s t | s <- ss ]
gtSPO1 _ _        _ = bottom

gtSPO23 :: TRS -> Term -> Term -> Formula
gtSPO23 a s@(F f ss) t@(F g ts) = 
  conj [ conj [ varGtSPO a s tj | tj <- ts ],
         disj [ encodeGtSq s t,
                if f == g then conj [ encodeGeqSq s t, lexGtSPO a ss ts ] else bottom ] ]
gtSPO23 _ _ _ = bottom

lexGtSPO :: TRS -> [Term] -> [Term] -> Formula
lexGtSPO _ [] [] = bottom
lexGtSPO a (s : ss) (t : ts)
  | s == t    = lexGtSPO a ss ts
  | otherwise = varGtSPO a s t
lexGtSPO _ _ _ = error "lexGtSPO"

encodeGtMSPO :: TRS -> Term -> Term -> Formula
encodeGtMSPO a s t = conj [ encodeGeqA 1 s t, encodeGeqA 2 s t, varGtSPO a s t]

encodeSPO :: Signature -> TRS -> (Formula, [(Rule, Formula)])
encodeSPO sig trs =
  (conj (Distinct [ varPrec f | (f, _) <- sig ] :
         encodeWellDef 1 (markSignature sig) :
         encodeWellDef 2 (markSignature sig) :
         [ implies (varGtSPO a s t) (gtSPO a s t) | (s, t) <- a ]),
   [ ((l, r), encodeGtMSPO a l r) | (l, r) <- trs ])
  where 
    a = nub [ Rule.rename "x" 1 (s, t) | (l, r) <- trs, s <- subterms l, t <- subterms r ]

-- decoding

decodePrecedence :: Model -> Signature -> Precedence
decodePrecedence model sig = [ g | (g, _) <- sortOn (\(_, k) -> - k) a ]
  where a = [ (f, evalExp model (varPrec f)) | (f, _) <- sig ]

decodeSPO :: Model -> Signature -> SPO.Parameter
decodeSPO model sig =
  (decodeAlgebra 1 model (markSignature sig),
   decodeAlgebra 2 model (markSignature sig),
   decodePrecedence model sig)
