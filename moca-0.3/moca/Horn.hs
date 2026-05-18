module Horn
  (encodeTPTP, encodeINF, encodeINF_noCondition, splitIf, multiSplitIf, tupling,
  trueSymbol, falseSymbol, trueTerm, falseTerm,
  SplitIfInfo, SplitIfEntry, RightInliningInfo, CertInfo, splitIf_cert, deleteConditions_cert)
where

import Data.List
import Data.Ord
import Text.Read
import Lists
import Terms
import Rules
import Substitutions
import TPTP
import INF
import Parameters

import Debug.Trace

-- Checking if a Horn cluase admits a trivial model.

-- Satisfiability checker of propositional Horn formulas

deleteAll x ys = [ y | y <- ys, y /= x ]

satisfiable :: Eq a => [HornClause a] -> Bool
satisfiable cs = satisfiable1 cs cs

satisfiable1 cs1 []                   = True
satisfiable1 cs1 (([], Nothing) : cs) = False
satisfiable1 cs1 (([], y@(Just a)) : cs) = satisfiable cs2 
  where cs2 = [ (deleteAll a xs, z) | (xs, z) <- cs1, y /= z ]
satisfiable1 cs1 (_ : cs) = satisfiable1 cs1 cs

encodeTPTP :: TPTP -> Maybe [HornClause Atom]
encodeTPTP tptp = sequenceA [ encodeClause clause | CNF _ _ clause <- tptp ]

encodeINF :: INFProblem -> [HornClause Atom]
encodeINF (SemiEquational ceses)   = infToHorn ceses
encodeINF (Join ceses)             = infToHorn ceses
encodeINF (Oriented ceses)         = infToHorn ceses
infToHorn :: (CES, ES) -> [HornClause Atom]
infToHorn (ces, es) = [ (toAtoms es', Just (Equation l r)) | (es', (l, r)) <- ces ++ [ceqForCondition es] ] 
                   ++ [([Equation trueTerm falseTerm], Nothing)]
  where ceqForCondition es = (es, (trueTerm, falseTerm))
        toAtoms es = [ Equation l r | (l, r) <- es ]

encodeINF_noCondition :: INFProblem -> [HornClause Atom]
encodeINF_noCondition (SemiEquational ceses)   = infToHorn_noCondition ceses
encodeINF_noCondition (Join ceses)             = infToHorn_noCondition ceses
encodeINF_noCondition (Oriented ceses)         = infToHorn_noCondition ceses
infToHorn_noCondition :: (CES, ES) -> [HornClause Atom]
infToHorn_noCondition (ces, es) = infToHorn (deleteConditions ces, es)
  where deleteConditions ces = [ ([], e0) | (es0, e0) <- ces ] 

        
encodeClause []                               = Just ([], Nothing)
encodeClause ((True, z) : clause)
  | Just (xs, Nothing) <- encodeClause clause = Just (xs, Just z)
encodeClause ((False, z) : clause)
  | Just (xs, ys) <- encodeClause clause      = Just (z : xs, ys)
encodeClause _ = Nothing 


rootOfPredicate (Predicate (F f _)) = Just f
rootOfPredicate (Equation _ _)      = Nothing

propositionalEncoding hornClauses =
  [ ([ f | Predicate (F f _) <- ts ], Nothing)
  | (ts, Nothing) <- hornClauses ] ++
  [ ([ f | Predicate (F f _) <- ts ], Just g)
  | (ts, Just (Predicate (F g _))) <- hornClauses ]

hasTrivialModel :: [HornClause Atom] -> Bool
hasTrivialModel hornClauses = satisfiable (propositionalEncoding hornClauses)

-- Trasformation from Horn clauses to word problems
-- (Claessen and Smallbone, IJCAR 2018)

-- for certificate generation

-- split-if
type SplitIfEntry = (CEquation, String, [Term])
type SplitIfInfo = [SplitIfEntry]

-- CES: resulting CTRS
-- CEquation: original crule (before right-inlining)
-- [(Term, Term)]: inlined conditions
type RightInliningInfo = (CES, [(CEquation, [(Term, Term)])])

type CertInfo = (SplitIfInfo, RightInliningInfo)

trueSymbol  = "true__"
falseSymbol = "false__"
trueTerm    = F trueSymbol []
falseTerm   = F falseSymbol []

liftAtom :: Atom -> (Term, Term)
liftAtom (Predicate t)  = (t, trueTerm)
liftAtom (Equation s t) = (s, t)

liftHornClause :: HornClause Atom -> CEquation
liftHornClause (ps, Nothing) =
  ([ liftAtom p | p <- ps], (falseTerm, trueTerm))
liftHornClause (ps, Just e)  =
  ([ liftAtom p | p <- ps], liftAtom e)

liftHornClauses :: [HornClause Atom] -> CES
liftHornClauses hornClauses = [ liftHornClause c | c <- hornClauses ]

fresh :: Char -> Int -> String
fresh f n = f : show n

functionsInCES ces = functionsInES [ e' | (es, e) <- ces, e' <- e : es ]

fSuffix :: Char -> String -> Maybe Int
fSuffix f (f' : s) | f == f' =  readMaybe s
fSuffix f _                  = Nothing

fIndex f ces =
  foldl max 0 [ n | f0 <- functionsInCES ces, Just n <- [fSuffix f f0] ] + 1


tuplingCES' :: [(Int, Parameter)] -> Int -> CES -> ES
tuplingCES' lprms n [] = []
tuplingCES' lprms n (([], e) : ces) = e : tuplingCES' lprms n ces
tuplingCES' lprms n (ce@(es, (u, v)) : ces) =
  (F f (esL ++ ws), u) : (F f (esR ++ ws), v) : tuplingCES' lprms (n + 1) ces
  where
    f = fresh 't' n
    esL = [ l | (l, _) <- es ]
    esR = [ r | (_, r) <- es ]
    ws | splitIfwithAllVariablesMode lprms  = [ V x | x <- nub (vL ++ vR ++ vars u ++ vars v) ]
       | otherwise             = [ V x | x <- nub (vs ++ vars u ++ vars v) ]
    vL = [ v | t <- esL, v <- vars t]
    vR = [ v | t <- esR, v <- vars t]
    vs = if length vL < length vR then vL else vR

tuplingCES :: [(Int, Parameter)] -> CES -> ES
tuplingCES lprms ces = tuplingCES' lprms (fIndex 't' ces) ces

tupling :: [(Int, Parameter)] -> [HornClause Atom] -> (ES, Equation, Maybe CertInfo)
tupling lprms hornClauses
  = if hasTrivialModel hornClauses then
      ([], (trueTerm, falseTerm), Nothing)
    else
      (tuplingCES lprms (inlining (liftHornClauses hornClauses)), (trueTerm, falseTerm), Nothing)

splitIfCES' :: [(Int, Parameter)] -> Int -> CES -> ES
splitIfCES' lprms n [] = []
splitIfCES' lprms n (([], e) : ces) = e : splitIfCES' lprms n ces
splitIfCES' lprms n (ce@((s0, t0) : es, (u, v)) : ces)  =
  (F f (s : ws), u) : splitIfCES' lprms (n + 1) ((es, (F f (t : ws), v)) : ces)
  where
    f = fresh 'f' n
    ws | splitIfwithAllVariablesMode lprms  = [ V x | x <- nub (vars s0 ++ vars t0 ++ vars u ++ vars v) ]
       | otherwise             = [ V x | x <- nub (vars s ++ vars u ++ vars v) ]
    (s, t) = if length (vars s0) < length (vars t0) then (s0, t0) else (t0, s0)

splitIfCES :: [(Int, Parameter)] -> CES -> ES
splitIfCES lprms ces = splitIfCES' lprms (fIndex 'f' ces) ces

splitIf :: [(Int, Parameter)] -> [HornClause Atom] -> (ES, Equation, Maybe CertInfo)
splitIf lprms hornClauses
  = if hasTrivialModel hornClauses then
      ([], (trueTerm, falseTerm), Nothing)
    else
      (splitIfCES lprms (inlining (liftHornClauses hornClauses)), (trueTerm, falseTerm), Nothing)

multiSplitIfCES :: CES -> CES
multiSplitIfCES ces = multiSplitIfCES' (fIndex 'g' ces) ces

multiSplitIfCES' :: Int -> CES -> CES
multiSplitIfCES' n ces 
  | (is, tps) : _ <- sortByLengthOfFirst (cases ces)  
    = multiSplitIfCES' (n + 1) (otherCES is ++ newCES tps)
  where otherCES is0 = [ ce | (i, ce) <- zip [0..] ces, i `notElem` is0 ] 
        newCES tps0 = [ ([], (newLhs n s tps0, t))  | (s, t) <- tps0 ] 
        newLhs n0 s0 tps0 = F (fresh 'g' n0) (s0 : (variableParts tps0))
        cases ces0 =  [ (indices cands, tps) 
                      | cands <- powerset (oneAssumptionCES (zip [0..] ces0)), 
                        length cands >= 2,
                        length cands <= 4,
                        (es1, es2) <- toESPairs cands,
                        commonFirstElements es1, commonFirstElements es2,
                        let ((s1, _) : _, (t1, _) : _) = (es1, es2),
                        let tps = (s1, t1) : [ (s, t) | ((_, s), (_, t)) <- zip es1 es2]
                      ]
        oneAssumptionCES nces0 = [ nce | nce@(_, (es, _)) <- nces0, length es == 1 ] 
        indices cands0 = [ i | (i, _) <- cands0 ]
        toESPairs cands0 = [ unzip eps 
                           | eps <- takeEach [ invertedEquations e1 e2 | (_, ([e1], e2)) <- cands0 ] ]
        invertedEquations e0 e0' = [ (e1, e2) | e1 <- symmetric [e0], e2 <- symmetric [e0'] ]
        variableParts tpairs0 = minLength [ varsExceptFor k tpairs0 | k <- [0..(length tpairs0 - 1)] ]
        varsExceptFor k tpairs0 = nub [ V x | (i, (s, t)) <- zip [0..] tpairs0, 
                                              x <- if i == k then vars s else vars s ++ vars t ] 
        minLength xss = head [ xs0 | (_, xs0) <- sortBy (comparing fst) [ (length xs, xs) | xs <- xss ] ]
multiSplitIfCES' n ces  = ces
    -- e.g. toESPairs [ (s1 = s2 => t1 = t2), (s1 = s3 => t1 = t3) ] 
    --        = [ unzip eps | eps <- takeEach [ [(s1 = s2, t1 = t2), ..., (s2 = s1, t2 = t1)], [(s1 = s3, t1 = t3), ..., (s3 = s1, t3 = t1)] ] ]
    --        = [ unzip eps | eps <- [ [(s1 = s2, t1 = t2), (s1 = s3, t1 = t3)], [(s1 = s2, t2 = t1), (s1 = s3, t1 = t3)], ... ] ]
    --        = [ ([s1 = s2, s1 = s3], [t1 = t2, t1 = t3]), ([s1 = s2, s1 = s3], [t2 = t1, t1 = t3]), ... ]
    -- e.g. invertedEquations (s1 = s2) (t1 = t2) = [(s1 = s2, t1 = t2), (s1 = s2, t2 = t1), (s2 = s1, t1 = t2), (s1 = t1, s2 = t2)]

multiSplitIf :: [(Int, Parameter)] -> [HornClause Atom] -> (ES, Equation, Maybe CertInfo)
multiSplitIf lprms hornClauses
  = if hasTrivialModel hornClauses then
      ([], (trueTerm, falseTerm), Nothing)
    else
      (tuplingCES lprms (multiSplitIfCES (inlining (liftHornClauses hornClauses))), (trueTerm, falseTerm), Nothing)

sortByLengthOfFirst :: Ord a => [([a],b)] -> [([a],b)]
sortByLengthOfFirst xsps 
  = [ xsp0 | (_, xsp0) <- sortBy (comparing (Down . fst)) [ (length xs, xsp) | xsp@(xs, _) <- xsps ] ]

-- e.g. inlining [ ( [(min(x,y), z), (f(z), c)], (g(x, z), c) ) ]
--       = [ ( [(f(min(x,y)), c)], (g(x, min(x,y)), c) ) ]

inlining :: CES -> CES
inlining ces = [ inlining' ce | ce <- ces ]
inlining' :: CEquation -> CEquation
inlining' (es, e) 
  | solvedForms es == []    
    = (es, e)
  | sgm : _ <- solvedForms es  
    = inlining' (removeTrivialEquations (substituteES es [sgm]), 
                           substituteEquation e [sgm])
  where solvedForms es0 = [ (x, r) | (V x, r) <- symmetric es0, x `notElem` vars r ]

-- certifiable split-if by CeTA
-- TODO
-- * optimize variables to append (see tupling)
-- * inlining (right/left) (could be strengthened if only disproof is considered)

similarCEquation :: CEquation -> CEquation -> Bool
similarCEquation (cs1, (l1, r1)) (cs2, (l2, r2)) =
  variant (F "" (l1 : map fst cs1)) (F "" (l2 : map fst cs2))

groupCES :: CES -> [[CEquation]]
groupCES [] = []
groupCES (ce : ces) = case partition (similarCEquation ce) ces of
  (xs, ys) -> (ce : xs) : groupCES ys

-- splitIfCES''_cert lprms n gs i
-- gs is grouped CES
splitIfCES''_cert :: [(Int, Parameter)] -> Int -> [[CEquation]] -> SplitIfInfo -> (ES, SplitIfInfo)
splitIfCES''_cert lprms n [] i = ([], i)
splitIfCES''_cert lprms n ([] : gs) i =  error "empty group of conditional equations is found" -- this error implies a bug

splitIfCES''_cert lprms n (g@(([], _) : _) : gs) i =
-- when the group consists of only unconditional equations
  case splitIfCES''_cert lprms n gs i of
    (es', i') -> (map snd g ++ es', i')
splitIfCES''_cert lprms n (([ce@(cs, (l, r))]) : gs) i =
-- the case when the group is singleton
-- in this case we use tupling, which optimizes the number of variables appended
  case splitIfCES''_cert lprms (n+1) gs i of
    (es', i') -> ((l, F f (map fst cs ++ ws)) : (F f (map snd cs ++ ws), r) : es', (ce, f, ws) : i')
  where
    f = fresh 'c' n
    vL = [ v | (t, _) <- cs, v <- vars t ]
    vR = [ v | (_, t) <- cs, v <- vars t ]
    vs = if length vL < length vR then vL else vR
    ws = [ V x | x <- nub (vs ++ vars l ++ vars r)]
splitIfCES''_cert lprms n (g : gs) i = 
  case splitIfCES''_cert lprms (n + 1) gs i of
    (es', i') -> (concat (map fst unraveled) ++ es', map snd unraveled ++ i')
  where
    ws ce = [ V x | x <- varsInCEq ce  ] -- TODO: could be optimized?
    f = fresh 'c' n
    -- NOTE: length (ws ce1) and length (ws ce2) may vary for ce1, ce2 in g.
    -- For example, see COPS #882 after inlining:
    -- ce1: last(cons(x, y)) -> x | y = nil
    -- ce2: last(cons(x, y)) -> last(y) | y = cons(u, v)
    -- For handling this, we insert dummy variables so that arities are consistent.
    k = maximum [ length (ws ce) | ce <- g ]
    dummyVariables ce =
      let xs = [ V x  | i <- [0..], let x = "X" ++ show i, notElem x (varsInCEq ce) ]
      in take (k - length (ws ce)) xs 
    unraveled = [ ([e1, e2], (ce, f, auxVars))
                | ce@(cs, (u, v)) <- g,
                  let auxVars = ws ce ++ dummyVariables ce,
                  let e1 = (u, F f (map fst cs ++ auxVars)),
                  let e2 = (F f (map snd cs ++ auxVars), v) ]

splitIfCES_cert :: [(Int, Parameter)] -> CES -> (ES, SplitIfInfo)
splitIfCES_cert lprms ces = splitIfCES''_cert lprms (fIndex 'c' ces) (groupCES ces) []

rightInlining_cert' :: CEquation -> (CEquation, [(Term, Term)]) 
rightInlining_cert' crule@(cs, (l, r)) =
  case pick cs of
    Nothing -> (crule, [])
    Just ((x, s), cs') ->
      case rightInlining_cert' ([ (substitute s' [(x, s)], t') | (s', t') <- cs' ], (l, substitute r [(x, s)])) of
        (crule', cs'') -> (crule', (s, V x) : cs'')
  where
    pick' acc [] = Nothing
    pick' acc ((s, t) : cs) =
      case t of
        V x | notElem x [ v | u <- l : s : map snd (acc ++ cs), v <- vars u ]
          -> Just ((x, s), reverse acc ++ cs)
        _ -> pick' ((s, t) : acc) cs
    pick cs = pick' [] cs

-- faithful implementation of Lemma 3 (Sternagel and Sternagel 2017)
rightInlining_cert :: CES -> RightInliningInfo
rightInlining_cert ctrs = (ctrs', info)
  where
    ctrs' = map fst [ rightInlining_cert' crule | crule <- ctrs ]
    info = [ (crule, cs)  | crule <- ctrs, let (_, cs) = (rightInlining_cert' crule), cs /= [] ]

splitIf_cert :: [(Int, Parameter)] -> [HornClause Atom] -> (ES, Equation, Maybe (SplitIfInfo, RightInliningInfo))
splitIf_cert lprms hornClauses
  = if hasTrivialModel hornClauses then
      ([], (trueTerm, falseTerm), Nothing)
    else
      case rightInlining_cert (liftHornClauses hornClauses) of
        i@(ces, _) ->
          case splitIfCES_cert lprms ces of
            (es, i') -> (nub es, (trueTerm, falseTerm), Just (i', i))

deleteConditions_cert :: [(Int, Parameter)] -> [HornClause Atom] -> (ES, Equation, Maybe (SplitIfInfo, RightInliningInfo))
deleteConditions_cert lprms hornClauses =
  (nub es, (trueTerm, falseTerm), Just ([], (ces, [])))
  where
    ces =  liftHornClauses hornClauses
    es = [ e | (_, e) <- ces]
