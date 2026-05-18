module EncodingToZ3 where

import Terms
import Rules
import LPOPrecedenceCondition

import Data.List

lTagSuffix = "R"


inputForZ3 :: [String] -> [(String, Rule)] -> [[String]] -> String
inputForZ3 smallsymbols tagrs tagss = decint ++ decbool ++ decbool_reducible ++ avoidbug 
                              ++ neq ++ equiv ++ equiv_reducible ++ lpocond ++ truecond ++ precedencecond ++ getval
      where trs = [r | (_, r) <- tagrs]
            tags = [v | (v, _) <- tagrs]
            symbols = functionsInES trs
            decint = intercalate "\n" ["(declare-fun " ++ s ++ " () Int)" | s <- symbols]
            decbool = intercalate "\n" ["(declare-fun " ++ v ++ " () Bool)" | v <- tags]
            decbool_reducible = intercalate "\n" ["(declare-fun " ++ v ++ lTagSuffix ++ " () Bool)" | v <- tags]
            avoidbug = "\n(declare-fun xxxxx () Int)\n(assert (> xxxxx 0))\n"
            neq = if ps == [] then "" else "(assert (and " ++ intercalate " " ps ++ "))"
              where ps = [ "(not (= " ++ s1 ++ " " ++ s2 ++ "))" | (i, s1) <- zip [0..] symbols,
                                                                   (j, s2) <- zip [0..] symbols, 
                                                                    i < j]
            equiv = if ps == [] then "" else "(assert (and " ++ intercalate " " ps ++ "))"
              where ps = [ show (equivalentCondition v r) | (v, r) <- tagrs]
            -- equiv = intercalate "\n" ["(assert " ++ show (equivalentCondition v r) ++")" | (v, r) <- tagrs]
            rtagls = [(v ++ lTagSuffix, l) | (v, (l, _)) <- tagrs ]    --- TODO declare earlier
            equiv_reducible = "(assert " ++ show (conditionForReducibility tagrs rtagls) ++")"
            -- lpocond = assertCondition1 trs
            -- lpocond = assertCondition2 trs
            -- lpocond = assertCondition3 tagrs
            lpocond = assertCondition4 rtagls
            truecond = if ps == [] then "" else "(assert (and " ++ intercalate " " ps ++ "))"
              where ps = [ show (existTrue tagrs tags') | tags' <- tagss ]
            precedencecond = if ps == [] then "" else "(assert (and " ++ intercalate " " ps ++ "))"
              where ps = ["(> " ++ s ++ " " ++ t ++")" | s <- symbols, s `notElem` smallsymbols, t <- smallsymbols ]  
                                
            getval = "(check-sat)(get-value (" ++ intercalate " " (symbols ++ tags) ++ "))"


-- assertCondition1 :: ES -> String
-- assertCondition1 es = intercalate "\n" ["(assert-soft " ++ show (precedenceConditions e) ++")" 
--                                           | e <- es, precedenceConditions e /= Val True, precedenceConditions e /= Val False]

-- assertCondition2 :: ES -> String
-- assertCondition2 es = intercalate "\n" ["(assert-soft " ++ show (precedenceConditions e) ++")" 
--                                           | e <- es', precedenceConditions e /= Val True, precedenceConditions e /= Val False]
--     where es' = [e2 | e1@(l1, r1) <- es, 
--                          e2@(l2, r2) <- es, 
--                          e1 /= e2, 
--                          Just _ <- [aReduct [e2] l1]
--                          ]

-- assertCondition3 :: [(String, Rule)] -> String
-- assertCondition3 tagrs = intercalate "\n" ["(assert-soft " ++ show (Is v2) ++")" | v2 <- tagrs']
--     where tagrs' = [v2 | (v1, e1@(l1, _)) <- tagrs, 
--                          (v2, e2) <- tagrs, 
--                          e1 /= e2, 
--                          Just _ <- [aReduct [e2] l1]
--                          ]

assertCondition4 :: [(String, Term)] -> String
assertCondition4 rtagls = intercalate "\n" ["(assert-soft " ++ show (Is v2) ++")" | (v2, _) <- rtagls]

existTrue :: [(String, Rule)] -> [String] -> InequalityFormula
existTrue tagrs tags = disjunction [Is v | (v, _) <- tagrs, notElem v tags]

equivalentCondition :: String -> Rule -> InequalityFormula
equivalentCondition v r = equivalence (Is v) (precedenceConditions r)

--- P1 can rewrite Q1 Q2
--- P2 can rewrite    Q2 Q3
--- P3 can rewrite    Q2    Q4
----- then formulas are the followings: 
----- P1 -> Q1 & Q2
----- P2 -> Q2 & Q3
----- P3 -> Q2 & Q4
----- Q1 -> P1
----- Q2 -> P1 | P2 | P3
----- Q3 -> P2
----- Q4 -> P3
conditionForReducibility :: [(String, Rule)] -> [(String, Term)] -> InequalityFormula
conditionForReducibility tagrs rtagls 
  = conjunction (
      [ implication (Is v) (conjunction [ Is v2 | v2 <- v2s ]) | (v, v2s) <- relvv2 ]  
      ++  [ implication (Is v2) (disjunction [ Is v | (v, v2s) <- relvv2, v2 `elem` v2s ] ) | (v2, _) <- rtagls ]
    )
  where 
    relvv2 = [ (v,  [ v2 | (v2, l) <- rtagls, not (inNF [e] l) ]) | (v, e) <- tagrs ]
                              