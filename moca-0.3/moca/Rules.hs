module Rules where

import Terms
import Substitutions
import Data.List
import Data.Ord

import Debug.Trace

type Precedence = [String]
showPrecedence :: Precedence -> String
showPrecedence prec = "\t" ++ intercalate " > " prec

type QuotientPrecedence = [[String]]

data EquationOrRule = E Equation | R Rule deriving Eq
instance Show EquationOrRule where
  show (E (l, r))    = show l ++ " = " ++ show r
  show (R (l, r))    = show l ++ " -> " ++ show r

type OTRS = (ES, TRS, Precedence)
showOTRS :: OTRS -> String
showOTRS (es, trs, prec)  = showES es ++ "\n" 
                            -- ++ "TRS:\n" 
                            ++ showTRS trs ++ "\n"
                            ++ "with the LPO induced by\n"
                            ++ showPrecedence prec

type XOTRS = (ES, TRS, [Precedence])

type HornClause a = ([a], Maybe a)
-- E.g.,
--   ([1,2,3], Just 4)  stands for "(1 && 2 && 3) -> 4".
--   ([1,2,3], Nothing) stands for "(1 && 2 && 3) -> False".
showHornClause :: Show a => [HornClause a] -> String
showHornClause hcs = tab ++ intercalate "\n\t" 
                              [ showAntecedents as ++ showConsequence mc | (as, mc) <- hcs]
  where showAntecedents [] = ""
        showAntecedents as = intercalate " & " [ show a | a <- as ] ++ " ==> "
        showConsequence (Just c) = show c 
        showConsequence Nothing  = "\\bottom"
        tab | null hcs  = ""
            | otherwise = "\t"

-- Conditional equations (used as intermediate data)
type CEquation = ([Equation], Equation)
type CES = [CEquation]


-- check if two rules are identical except for variables
isSameRule :: Rule -> Rule -> Bool
isSameRule (l1, r1) (l2, r2) = variant (F "" [l1, r1]) (F "" [l2, r2])

-- check if two terms are variant
variant :: Term -> Term -> Bool
variant s t = variant' [] [(s, t)]
variant' :: [(String, String)] -> ES -> Bool
variant' vps []                                     = True
variant' vps ((F _ _, V _) : _)                     = False
variant' vps ((V _, F _ _) : _)                     = False
variant' vps ((F f ts1, F g ts2) : es) | f == g && length ts1 == length ts2 = variant' vps (zip ts1 ts2 ++ es)
                                       | otherwise  = False
variant' vps ((V x, V y) : es) 
  | or [ (v1 == x && v2 /= y) || (v1 /= x && v2 == y) | (v1, v2) <- vps ]  = False
  | otherwise                                                              = variant' ((x,y) : vps) es

-- check if two rules are identical except for variables
isSameEquation :: Rule -> Rule -> Bool
isSameEquation (l1, r1) (l2, r2) = isSameRule (l1, r1) (l2, r2)  
                                || isSameRule (l1, r1) (r2, l2) 
                                || isSameRule (r1, l1) (l2, r2) 
                                || isSameRule (r1, l1) (r2, l2) 



sizeOfEquation :: Rule -> Int
sizeOfEquation (s, t) = size s + size t
sizeOfES :: ES -> Int
sizeOfES rs = sum [ sizeOfEquation r | r <- rs ]



-- solve matching problem l <~ t (Search substitution sgm s.t. l sgm = t)
-- Note: We convert matching problem to unification problem by regarding variables in rhs as constants.
match :: Term -> Term -> Maybe Subst
match s t = match' [] [(s,t)]
match' :: Subst -> ES -> Maybe Subst
match' sgm []                                     = Just sgm
match' sgm ((F f ts1, F g ts2) : es) | f == g     = match' sgm (zip ts1 ts2 ++ es)
                                     | otherwise  = Nothing
match' sgm ((F f ts1, V x) : es)                  = Nothing
match' sgm ((V x, t) : es) | and [ t == s | (y, s) <- sgm, x == y ]  = match' ((x, t) : sgm) es
                           | otherwise                               = Nothing

-- find an mgu for two terms
mgu :: Term -> Term ->  Maybe Subst
mgu s t = fst (mgu' ([], [(s, t)]))
mgu' :: (Subst,  ES) -> (Maybe Subst, ES)
mgu' (sgm, [])                                          = (Just sgm, [])
mgu' (sgm, (F f ts1, F g ts2) : es) | f == g            = mgu' (sgm, zip ts1 ts2 ++ es)
mgu' (sgm, (V v    , V w    ) : es) | v == w            = mgu' (sgm, es)
mgu' (sgm, (F f ts , V v    ) : es)                     = mgu' (sgm, (V v, F f ts) : es)
mgu' (sgm, (V v    , t      ) : es) | not (occurs v t)  = mgu' (update v t sgm, substituteES es [(v, t)])
mgu' (sgm, (s      , t      ) : es)                     = (Nothing, [])



-- get a reduct of term s: find t such that s ->_R t
aReduct :: TRS -> Term -> Maybe Term
aReduct rs s | t : _ <- allReducts rs s  = Just t
             | otherwise                 = Nothing

aReductWithUsedRule :: TRS -> Term -> Maybe (Term, Rule)
aReductWithUsedRule rs s | tr : _ <- allReductsWithUsedRule rs s  = Just tr
                         | otherwise                              = Nothing

-- get all reducts of term s (w.r.t. ->_R) 
allReducts :: TRS -> Term -> [Term]
allReducts trs s = [ t | (t, _) <- allReductsWithUsedRule trs s ]

allReductsWithUsedRule :: TRS -> Term -> [(Term, Rule)]
allReductsWithUsedRule trs s = [ (replace s (substitute r sgm) p, (l, r))
                               | p <- allPositions s,
                                 (l, r) <- trs,
                                 Just sgm <- [match l (subtermAt s p)] ]

-- check whther term s is normal form
isNormalForm trs s = null (allReducts trs s)

-- get a normal form (input: TRS and term)
normalize :: TRS -> Term -> Term
normalize rs t | Just t <- aReduct rs t  = normalize rs t
               | otherwise               = t

-- get all normal form of term t 
allNormalForms :: TRS -> Term -> [Term]
allNormalForms trs t | null (allReducts trs t)  = [t]
                     | otherwise                = [ u | s <- allReducts trs t, u <- allNormalForms trs s ]

inNF :: TRS -> Term -> Bool
inNF trs t = allReducts trs t == []

-- check whether t1 ->* *<- t2
isJoinable :: TRS -> Term -> Term -> Bool
isJoinable trs t1 t2 = or [ s1 == s2 | s1 <- allNormalForms trs t1, s2 <- allNormalForms trs t2 ]


lrReduction :: TRS -> ES -> ES
lrReduction trs es = nubBy isSameEquation (removeTrivialEquations [ (normalize trs s, normalize trs t) | (s, t) <- es] )


interReduction :: TRS -> TRS
interReduction trs = interReduction2 (removeTrivialEquations [(s, normalize trs t)| (s, t) <- trs] )
interReduction2 trs 
  = [ (s, t) | (s, t) <- trs, normalize (removeRule (s, t) trs) s /= t ] 
    where removeRule r trs = [ r0 | r0 <- trs, not (isSameRule r r0) ]



removeTrivialEquations :: TRS -> TRS
removeTrivialEquations trs = [ (s, t) | (s, t) <- trs, s /= t ]

inverse :: ES -> ES
inverse es = [ (r, l) | (l, r) <- es ]

symmetric :: ES -> ES
symmetric es = nubBy isSameRule (es ++ inverse es)

equationInES :: Equation -> ES -> Bool
equationInES e es = or [ isSameEquation e e' | e' <- es ]
ruleInTRS :: Rule -> TRS -> Bool
ruleInTRS r trs = or [ isSameRule r r' | r' <- trs ]

subES :: ES -> ES -> Bool
subES es1 es2 = and [ equationInES e es2  | e <- es1 ]
subTRS :: TRS -> TRS -> Bool
subTRS trs1 trs2 = and [ ruleInTRS r trs2  | r <- trs1 ]

existCommonES :: ES -> ES -> Bool
existCommonES es1 es2 = or [ equationInES e es2  | e <- es1 ]
existCommonTRS :: TRS -> TRS -> Bool
existCommonTRS trs1 trs2 = or [ ruleInTRS r trs2  | r <- trs1 ]

identicalES :: ES -> ES -> Bool
identicalES es1 es2 = subES es1 es2 && subES es2 es1
identicalTRS :: TRS -> TRS -> Bool
identicalTRS trs1 trs2 = subTRS trs1 trs2 && subTRS trs2 trs1

identicalOTRS :: OTRS -> OTRS -> Bool
identicalOTRS (es1, trs1, prec1) (es2, trs2, prec2) = identicalES es1 es2 
                                                    && identicalTRS trs1 trs2 
                                                    && prec1 == prec2



functionsInTermOfArity :: Int -> Term -> [String]
functionsInTermOfArity n (V x) = []
functionsInTermOfArity n (F f ts) 
  | length ts == n  = nub (f : [ g | t <- ts, g <- functionsInTermOfArity n t ])
  | otherwise       = [ g | t <- ts, g <- functionsInTermOfArity n t ]

functionsInESOfArity :: Int -> ES -> [String]
functionsInESOfArity n es 
  = nub [ f | (s, t) <- es, f <- functionsInTermOfArity n s ++ functionsInTermOfArity n t ]

constants :: ES -> [String]
constants es = functionsInESOfArity 0 es

mixOfESAndTRS :: ES -> TRS -> [EquationOrRule]
mixOfESAndTRS es trs = [E e | e <- es] ++ [R r | r <- trs]

separateESAndTRS :: [EquationOrRule] -> (ES, TRS)
separateESAndTRS ers = ([ e | E e <- ers ], [ r | R r <- ers ])


constEquations :: ES -> ES
constEquations es = [ (s, t) |  (s, t) <- es, 
                                variant s t, 
                                and [ v `notElem` vars t | v <- vars s ] ]



-- show
showTRS :: TRS -> String
showTRS trs ="\t" ++ intercalate "\n\t" [ show s ++ " -> " ++ show t | (s, t) <- sortESByStr trs ]

showMaybeTRS :: Maybe TRS -> String
showMaybeTRS (Just trs) = "Just\n" ++  showTRS trs
showMaybeTRS Nothing    = "Nothing"

showES :: ES -> String
showES es = tab ++ intercalate "\n\t" [ show s ++ " = " ++ show t | (s, t) <- sortESByStr es ]
  where tab | es == []  = ""
            | otherwise = "\t"

showERs :: [EquationOrRule] -> String
showERs ers = showES es ++ nl ++ showTRS trs 
  where (es, trs) = separateESAndTRS ers 
        nl | es == []  = ""
           | otherwise = "\n"

sortESByStr :: ES -> ES
sortESByStr es = [ e | (_, e) <- sortBy (comparing fst) [ (show e, e) | e <- es ] ]

sortES :: ES -> ES
sortES  es = [ e | (_, e) <- sortBy (comparing fst) [ (sizeOfEquation e, e) | e <- es ] ]

sortERs :: [EquationOrRule] -> [EquationOrRule]
sortERs ers = [ er | (_, er) <- sortBy (comparing fst) [ (sizeOfER er, er) | er <- ers ] ]
  where sizeOfER (E e) = sizeOfEquation e
        sizeOfER (R r) = sizeOfEquation r


showCES :: CES -> String
showCES ces = intercalate "\n\t" [ showES es ++ "\n==>" ++ show e | (es, e) <- ces ]
        
replaceTermInParallel :: Term -> [(Position, Term)] -> Term
replaceTermInParallel t         pts | Just u <- lookup [] pts   = u
replaceTermInParallel t@(V _)   pts                             = t
replaceTermInParallel (F f ts)  pts                             = F f ts'    
  where ts' = [ replaceTermInParallel ti pts'
              | (ti, i) <- zip ts [0..],
                let pts' = [ (p, u) | (j : p, u) <- pts, i == j ] ]
replaceEquationInParallel :: Equation -> [((Position, String), Term)] -> Equation
replaceEquationInParallel (s, t) plrts 
  = (replaceTermInParallel s (pts' "L"), replaceTermInParallel t (pts' "R"))
  where pts' lr0 = [ (p, t) | ((p, lr), t) <- plrts, lr == lr0 ]


projectTerm :: [(String, Int)] -> Term -> Term
projectTerm fis t@(V _) = t
projectTerm fis (F f ts)  | Just i <- lookup f fis  = projectTerm fis (ts !! i)
                          | otherwise               = F f [ projectTerm fis t | t <- ts ]
projectEquation :: [(String, Int)] -> Equation -> Equation
projectEquation fis (s, t) = (projectTerm fis s, projectTerm fis t)
projectES :: [(String, Int)] -> ES -> ES
projectES fis es = [ projectEquation fis e | e <- es ]
{-
  memo: projectTerm [("f", 0), ("g", 0)] f(g(h(f(c)), d), c)
    = projectTerm [("f", 0), ("g", 0)] g(h(f(c)),d)
    = projectTerm [("f", 0), ("g", 0)] h(f(c))
    = h(projectTerm [("f", 0), ("g", 0)] f(c))
    = h(projectTerm [("f", 0), ("g", 0)] c)
    = h(c)
-}



differentRootSymbols :: Equation -> [String]
differentRootSymbols ((F f _), (V _))              = [f]
differentRootSymbols ((V _),   (F g _))            = [g]
differentRootSymbols ((F f _), (F g _))  | f /= g  = nub [f, g]
differentRootSymbols _                             = []
differentRootSymbolsInES :: ES -> [String]
differentRootSymbolsInES es = nub [ f | e <- es, f <- differentRootSymbols e ]

-- see Section 4.2.4 of Oi's master thesis
redundantEquationElimination :: ES -> ES
redundantEquationElimination es = [ e | e <- es, not (redundant e) ]
  where fs = [ f | f <- rootSymbolsInES es, 
                   f `notElem` insideFunctionSymbolsInES es,
                   f `notElem` differentRootSymbolsInES es ]
        redundant (V _  , _    ) = False
        redundant (_    , V _  ) = False
        redundant (F f _, F g _) = f `elem` fs || g `elem` fs

varsInCEq :: CEquation -> [String] 
varsInCEq (cs, (u, v)) =
  nub (vars u ++ vars v ++ [ x | (s, t) <- cs, x <- vars s ++ vars t ])
