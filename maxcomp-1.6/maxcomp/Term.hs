module Term where

import Data.List

type Signature = [(String, Int)]

data Term = V String | F String [Term] deriving Eq

type Subst = [(String, Term)]

type Position = [Int]

instance Show Term where
  show (V x)    = x
  show (F f ts) = f ++ "(" ++ intercalate "," [show t | t <- ts] ++ ")"

-- Var(t)

variables :: Term -> [String]
variables (V x) = [x]
variables (F _ ts) = nub [ x | t <- ts, x <- variables t ]

ground :: Term -> Bool
ground (V _)    = False
ground (F _ ts) = all ground ts

-- Fun(t)

functions :: Term -> [String]
functions (V _)    = []
functions (F f ts) = nub (f : [ g | t <- ts, g <- functions t ])

-- |t|
size :: Term -> Int
size (V _)    = 1
size (F _ ts) = 1 + sum [ size t | t <- ts ]

-- |t|_x
count :: Term -> String -> Int
count (V y) x
  | x == y    = 1
  | otherwise = 0
count (F _ ts) x = sum [ count t x | t <- ts ]

-- The list of all subterms of a term.
subterms :: Term -> [Term]
subterms t@(V _) = [t]
subterms t@(F _ us) = t : nub [ v | u <- us, v <- subterms u ]

properSubterms :: Term -> [Term]
properSubterms (V _)    = []
properSubterms (F _ ts) = [ u | t <- ts, u <- subterms t ]

-- Pos(t)
positions :: Term -> [Position]
positions (V _)    = [ [] ]
positions (F _ ts) = [] : [ i : p | (i, t) <- zip [0..] ts, p <- positions t ]

-- Pos_F(t)
functionPositions :: Term -> [Position]
functionPositions (V _)    = []
functionPositions (F _ ts) = 
  [] : [ i : p | (i, t) <- zip [0..] ts, p <- functionPositions t ] 

-- t|_p
subtermAt :: Term -> Position -> Term
subtermAt t        []      = t
subtermAt (F _ ts) (i : p) = subtermAt (ts !! i) p
subtermAt _        _       = error "subtermAt"

-- t[u]_p
replace :: Term -> Term -> Position -> Term
replace _        u []      = u
replace (F f ts) u (i : p) =
  F f [ if i == j then replace tj u p else tj | (j, tj) <- zip [0..] ts ]
replace _ _ _ = error "replace"

signatureOf :: Term -> Signature
signatureOf t = nub [ (f, length ts) | F f ts <- subterms t ]


-- t sigma
substitute :: Term -> Subst -> Term
substitute (V x) sigma
    | Just t <- lookup x sigma = t
    | otherwise                = V x
substitute (F f ts) sigma      = F f [ substitute t sigma | t <- ts ]

-- Dom(sigma)
domain :: Subst -> [String]
domain sigma = nub [ x | (x, _) <- sigma ]

-- x sigma tau = (x sigma) tau for all variables x
compose :: Subst -> Subst -> Subst
compose sigma tau =
  [ (x, substitute (substitute (V x) sigma) tau)
  | x <- nub (domain sigma ++ domain tau) ]

-- match l t = Just sigma if l sigma = t for some sigma
  
match' :: Subst -> [(Term, Term)] -> Maybe Subst
match' sigma [] = Just sigma
match' sigma ((V x, t) : ps)
  | m == Just t  = match' sigma ps
  | m == Nothing = match' ((x, t) : sigma) ps
  where m = lookup x sigma
match' sigma ((F f ss, F g ts) : ps)
  | f == g       = match' sigma (zip ss ts ++ ps)
match' _ _       = Nothing

match :: Term -> Term -> Maybe Subst
match s t = match' [] [(s,t)]

substituteES :: [(Term, Term)] -> Subst -> [(Term, Term)]
substituteES trs sigma = 
  [ (substitute l sigma, substitute r sigma) | (l, r) <- trs ]


-- Most general unifier

mgu' :: Subst -> [(Term, Term)] -> Maybe Subst
mgu' sigma [] = Just sigma
mgu' sigma ((V x, V y) : es)
  | x == y = mgu' sigma es
mgu' sigma ((V x, t) : es)
  | notElem x (variables t) =
      mgu' (compose sigma tau) (substituteES es tau)
  where tau = [(x, t)]
mgu' sigma ((s, t@(V _)) : es) = mgu' sigma ((t, s) : es)
mgu' sigma ((F f ss, F g ts) : es)
  | f == g = mgu' sigma (zip ss ts ++ es)
mgu' _ _ = Nothing

mgu :: Term -> Term -> Maybe Subst
mgu s t = mgu' [] [(s, t)]

unifiable :: Term -> Term -> Bool
unifiable s t = mgu s t /= Nothing

renameTerm :: String -> Int -> Term -> Term
renameTerm x k t = substitute t sigma
  where
    ys = variables t
    sigma = [ (y, V (x ++ show i)) | (y, i) <- zip ys [k :: Int ..]  ]

subsume :: Term -> Term -> Bool
subsume s t = match s t /= Nothing

variant :: Term -> Term -> Bool 
variant s t = subsume s t && subsume t s

mark :: String -> String
mark f = f ++ "#"

markSignature :: Signature -> Signature
markSignature sig = [ (g, n) | (f, n) <- sig, g <- [f, Term.mark f] ]

markTerm :: Term -> Term
markTerm (F f ts) = F (mark f) ts
markTerm _        = error "markTerm"
