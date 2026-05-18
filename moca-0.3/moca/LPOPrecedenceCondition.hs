module LPOPrecedenceCondition where

import Terms
import Rules
import Data.List
import Data.Ord

import Debug.Trace


data InequalityFormula = And [InequalityFormula]
                       | Or [InequalityFormula]
                       | Not InequalityFormula
                       | Gt String String
                       | Is String 
                       | Val Bool
                       deriving Eq
instance Show InequalityFormula where
    show (And [])    = "true"
    show (And fs)    = "(and " ++ intercalate " " [show f | f <- fs] ++ ")"
    show (Or [])     = "false"
    show (Or fs)     = "(or "  ++ intercalate " " [show f | f <- fs] ++ ")"
    show (Not f)     = "(not " ++ show f ++ ")"
    show (Gt e1 e2)  = "(> " ++ e1 ++ " " ++ e2 ++ ")"
    show (Is v)      = v
    show (Val True)  = "true"
    show (Val False) = "false"



precedenceConditions :: Rule -> InequalityFormula
precedenceConditions (        V _,           _)                 = Val False
precedenceConditions (  s@(F _ _),         V x)                 = Val (x `elem` vars s)
precedenceConditions (s@(F f ts1), t@(F g ts2)) | t `elem` ts1  = Val True
                                                | f /= g        = disjunction [lpo2a, lpo2b]
                                                | f == g        = disjunction [lpo2a, lpo2c]
  where lpo2a = disjunction [ precedenceConditions (u, t) | u <- ts1 ]
        lpo2b = conjunction [Gt f g, cond]
        lpo2c = conjunction [cond, lex]
        cond  = conjunction [ precedenceConditions (s, u) | u <- ts2 ]
        lex   | idx : _ <- [ i | (i, u) <- zip [0..] ts1, u /= ts2 !! i ]  
                  = precedenceConditions (ts1 !! idx, ts2 !! idx)
              | otherwise                                                  
                  = Val False

conjunction :: [InequalityFormula] -> InequalityFormula
conjunction [f]                       = f
conjunction fs | Val False `elem` fs  = Val False
               | nonT == []           = Val True
               | f : [] <- nonT       = f
               | otherwise            = And nonT
  where nonT = [ f | f <- fs, f /= Val True ]

disjunction :: [InequalityFormula] -> InequalityFormula
disjunction [f]                       = f
disjunction fs | Val True `elem` fs   = Val True
               | nonF == []           = Val False
               | f : [] <- nonF         = f
               | otherwise            = Or nonF
  where nonF = [ f | f <- fs, f /= Val False ]

negation :: InequalityFormula -> InequalityFormula
negation (Val True)  = Val False
negation (Val False) = Val True
negation f           = Not f

sortedPrecedence :: Maybe [(String, Int)] -> Maybe [String]
sortedPrecedence (Just fps) = Just [ f | (f, _) <- sortBy (comparing (Down . snd)) fps ]
sortedPrecedence Nothing    = Nothing

equivalence :: InequalityFormula -> InequalityFormula -> InequalityFormula
equivalence f1 f2 = disjunction [(conjunction [f1, f2]), (conjunction [negation f1, negation f2])]

-- f1 -> f2
implication :: InequalityFormula -> InequalityFormula -> InequalityFormula
implication f1 f2 = disjunction [negation f1, f2]

