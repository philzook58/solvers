module TRS where
    
import Data.List
import Term
import Rule

type TRS       = [Rule]
type Overlap   = (Rule, Position, Rule, Subst)

type Equation = (Term, Term)
type ES = [Equation]

showTRS :: TRS -> String
showTRS trs = unlines [ "  " ++ showRule rule | rule <- trs ]

showEq :: Rule -> String
showEq (l, r) = show l ++ " = " ++ show r

showES :: TRS -> String
showES es = unlines [ "  " ++ showEq e | e <- es ]

signatureOf :: TRS -> [(String, Int)]
signatureOf trs = nub [ fn | rule <- trs, fn <- Rule.signatureOf rule ]

substitute :: TRS -> Subst -> TRS
substitute trs sigma = [ Rule.substitute rule sigma | rule <- trs ]

variableCondition :: TRS -> Bool
variableCondition trs = all Rule.variableCondition trs

variables :: TRS -> [String]
variables trs = nub [ x | rule <- trs, x <- Rule.variables rule ]

-- Fun(R)

functions :: TRS -> [String]
functions trs = nub [ f | rule <- trs, f <- Rule.functions rule ]

functionsES :: ES -> [String]
functionsES es = TRS.functions es

-- D_R

definedSymbols :: TRS -> [String]
definedSymbols trs = nub [ f | (F f _, _) <- trs ]

substituteES :: TRS -> Subst -> TRS
substituteES = TRS.substitute

lhss :: TRS -> [Term]
lhss trs = [ l | (l, _) <- trs ]

-- Rewriting

-- [ u | t ->_R u ]
reducts :: TRS -> Term -> [Term]
reducts trs t =
  [ replace t (Term.substitute r sigma) p
  | p <- positions t,
    (l, r) <- trs,
    Just sigma <- [match l (subtermAt t p)] ]


-- A term u if t ->_R u.
rewrite :: TRS -> Term -> Maybe Term
rewrite trs t =
  case sortOn Term.size (reducts trs t) of
    []    -> Nothing
    u : _ -> Just u

rename :: String -> Int -> TRS -> TRS
rename x k trs = [ Rule.rename x k rule | rule <- trs ]

overlap :: TRS -> [Overlap]
overlap trs =
  [ ((l1, r1), p, (l2, r2), sigma)
  | rule2 <- trs,
    let (l2, r2) = Rule.rename "y" 0 rule2,
    p <- functionPositions l2,
    rule1 <- trs,
    p /= [] || not (Rule.variant rule1 rule2),
    let (l1, r1) = Rule.rename "x" 0 rule1,
    Just sigma <- [mgu l1 (subtermAt l2 p)] ]

nubES :: TRS -> TRS
nubES es = nubBy variantEq es

-- critical pairs
cp :: TRS -> TRS
cp trs =
  nubES [ Rule.rename "x" 0 (s, t)
        | ((_, r1), p, (l2, r2), sigma) <- overlap trs,
          let s = Term.substitute (replace l2 r1 p) sigma,
          let t = Term.substitute r2 sigma ]

-- p <_li q: left-inner order
left_inner :: Position -> Position -> Bool
left_inner []      _       = False
left_inner (_ : _) []      = True
left_inner (i : p) (j : q) = i < j || (i == j && left_inner p q)

-- leftmostInnermostRedex R t p checks if p in t is
-- a leftmost innermost redex in t for R when p is
-- a redex occurrence.
leftmostInnermostRedex :: TRS -> Term -> Position -> Bool
leftmostInnermostRedex trs (F _ ts) [] =
  all (normalForm trs) ts
leftmostInnermostRedex trs (F _ ts) (i : p) =
  all (normalForm trs) (take (i - 1) ts) &&
  leftmostInnermostRedex trs (ts !! i) p
leftmostInnermostRedex _ _ _ = error "leftmostInnermostRedex"

-- leftmost innermost critical pair

argumentNormalForm :: TRS -> Term -> Bool
argumentNormalForm _   (V _)    = True
argumentNormalForm trs (F _ ts) = all (normalForm trs) ts

liOverlaps :: TRS -> [Overlap]
liOverlaps trs =
  [ ((l1, r1), p, (l2, r2), sigma)
  | rule2@(l2, r2) <- trs2,
    p <- functionPositions l2,
    rule1@(l1, r1) <- trs1,
    p /= [] || not (Rule.variant rule1 rule2),
    Just sigma <- [mgu l1 (subtermAt l2 p)] ]
    where 
      trs1 = TRS.rename "x" 1 [ (l, r) | (l, r) <- trs, argumentNormalForm trs l ]
      trs2 = TRS.rename "y" 1 trs

licp :: TRS -> TRS
licp trs = 
  nubES [ Rule.rename "x" 0 (t, u)
        | ((_, r1), p, (l2, r2), sigma) <- liOverlaps trs,
          let s = Term.substitute l2 sigma,
          leftmostInnermostRedex trs s p,
          let t = Term.substitute (replace l2 r1 p) sigma,
          let u = Term.substitute r2 sigma ]

pcp :: TRS -> TRS
pcp trs = 
  nubES [ Rule.rename "x" 0 (t, u)
        | ((_, r1), p, (l2, r2), sigma) <- overlap trs,
          let s = Term.substitute l2 sigma,
          argumentNormalForm trs (subtermAt s p),
          let t = Term.substitute (replace l2 r1 p) sigma,
          let u = Term.substitute r2 sigma ]

normalForm :: TRS -> Term -> Bool
normalForm trs t = rewrite trs t == Nothing

reducible :: TRS -> Term -> Bool
reducible trs t = not (normalForm trs t)

remove :: Rule -> TRS -> TRS
remove rule trs =
  [ rule' | rule' <- trs, not (Rule.variant rule rule') ]

diff :: TRS -> TRS -> TRS
diff trs1 trs2 = foldl (\trs rule -> remove rule trs) trs1 trs2

elemEq :: Rule -> TRS -> Bool
elemEq e es = any (variantEq e) es

diffES :: TRS -> TRS -> TRS
diffES es1 es2 =
  [ e1 | e1 <- es1, not (elemEq e1 es2) ]

unionES :: TRS -> TRS -> TRS
unionES es1 es2 = nubES (es1 ++ es2)