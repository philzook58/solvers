module Terms where

import Lists
import Data.List
import Text.Read

-- [DATA] Term
data Term = V String | F String [Term] deriving Eq
instance Show Term where
  show (V x)    = x -- ++ "_"
  show (F f []) = f
  show (F f ts) = f ++ "(" ++ intercalate ", " [show t | t <- ts] ++ ")"

-- [TYPE]
type TermPair = (Term, Term)
type Position = [Int]
type Equation = TermPair
type ES = [Equation]
type Rule = TermPair
type TRS = [Rule]



-- variables in term
vars :: Term -> [String]
vars (V x)    = [x]
vars (F f ts) = nub [ x | t <- ts, x <- vars t ] 
varsInEquation :: Equation -> [String]
varsInEquation (s, t) = nub (vars s ++ vars t)
varsInES :: ES -> [String]
varsInES ps = nub [ x | p <- ps, x <- varsInEquation p ]

-- function symbols in term
functions :: Term -> [String]
functions (V x)    = []
functions (F f ts) = nub (f : [ g | t <- ts, g <- functions t ])
functionsInEquation :: Equation -> [String]
functionsInEquation (s, t) = nub (functions s ++ functions t)
functionsInES :: ES -> [String]
functionsInES ps = nub [ f | p <- ps, f <- functionsInEquation p ]

functionsWithArity :: Term -> [(String, Int)]
functionsWithArity (V x)    = []
functionsWithArity (F f ts) = nub ((f, length ts) : [ (g,m) | t <- ts, (g,m) <- functionsWithArity t ])

signatureOf :: [TermPair] -> [(String, Int)]
signatureOf ps = nub [ f | p <- ps, f <- functionsWithArity (fst p) ++ functionsWithArity (snd p)  ]

arity :: String -> [TermPair] -> Int
arity f trs = case lookup f (signatureOf trs) of
  Just m -> m
  Nothing -> error ("arity: the given function " ++ f ++ " is not found")

-- check whether string x exists in term t as a variable  
occurs :: String -> Term -> Bool
occurs x t = elem x (vars t)
occursInSomeTerm :: String -> [Term] -> Bool
occursInSomeTerm x ts = or [ occurs x t | t <- ts ]

-- get position list (Pos(t))
allPositions :: Term -> [Position]
allPositions (V x)    = [[]]
allPositions (F f ts) = [] : [ i : p | (i, t) <- zip [0..] ts, p <- allPositions t ]

functionPositions :: Term -> [Position]
functionPositions t = [ p | p <- allPositions t, F _ _ <- [subtermAt t p] ]

varPositions :: Term -> [Position]
varPositions t = [ p | p <- allPositions t, V _ <- [subtermAt t p] ]

-- p1 is upper than p2 (e.g. p1 = [1,2,1], p2 = [1,2,1,3])
upperPosition :: Position -> Position -> Bool
upperPosition p1 p2 = or [ p1 == take i p2  | i <- [0..length p2] ] 

-- get size of term (the cardinal of Pos(t))
size :: Term -> Int 
size t = length (allPositions t)

-- get subterm at p (t|_p)
subtermAt :: Term -> Position -> Term
subtermAt t        []       = t
subtermAt (F f ts) (n : ns) = subtermAt (ts !! n) ns

directSubterms :: Term -> [Term]
directSubterms (F _ ts) = ts
directSubterms _        = []

-- replace term by another term at p (t[u]_p)
replace :: Term -> Term -> Position -> Term
replace t        u []        = u
replace (F f ts) u (n : ns)  = F f [ arg i ti | (i, ti) <- zip [0..] ts ]
  where arg i ti | i == n    = replace ti u ns
                 | otherwise = ti 

-- replace function symbol f1 in term t by function symbol f2 if (f1, f2) <- ps
rename :: [(String, String)] -> String -> String
rename ps f  | Just g <- lookup f ps  = g
                    | otherwise              = f
replaceFunctionSymbol :: [(String, String)] -> Term -> Term
replaceFunctionSymbol ps (V x)     = V x
replaceFunctionSymbol ps (F f ts)  = F (rename ps f) [ replaceFunctionSymbol ps t | t <- ts ]
replaceFunctionSymbolsInES :: [(String, String)] -> ES -> ES
replaceFunctionSymbolsInES ps es = [ (replaceFunctionSymbol ps s, replaceFunctionSymbol ps t) | (s, t) <- es ]
           
originalString :: [(String, String)] -> String -> String
originalString fvdict g | Just g' <- lookup g [ (v, f) | (f, v) <- fvdict ] = g'
                        | otherwise                                         = g



insideFunctionSymbols :: Term -> [String]
insideFunctionSymbols t                 = nub [ f |               F _ us <- [t],    u <- us, f <- functions u ]
insideFunctionSymbolsInEquation :: Equation -> [String]
insideFunctionSymbolsInEquation (s, t)  = nub [ f |               F _ us <- [s, t], u <- us, f <- functions u ]
insideFunctionSymbolsInES :: ES -> [String]
insideFunctionSymbolsInES es            = nub [ f | (s, t) <- es, F _ us <- [s, t], u <- us, f <- functions u ]

rootSymbolsInEquation :: Equation -> [String]
rootSymbolsInEquation (s, t) = nub [ f | F f _ <- [s, t] ]
rootSymbolsInES :: ES -> [String]
rootSymbolsInES es = nub [ f | (s, t) <- es, F f _ <- [s, t] ]



systemPrefixF = "g"
systemPrefixV = "W"
freshFunctionSymbolNumber :: ES -> Int
freshFunctionSymbolNumber es 
  = 1 + (maximum (0 : [ n | f <- functionsInES es, Just n <- [readIntAfterPrefix systemPrefixF f] ]))
freshFunctionName :: Int -> String
freshFunctionName ffn = systemPrefixF ++ (show ffn)

freshVariableSymbolNumber :: ES -> Int
freshVariableSymbolNumber es 
  = 1 + (maximum (0 : [ n | v <- varsInES es, Just n <- [readIntAfterPrefix systemPrefixV v] ]))
freshVariableName :: Int -> String
freshVariableName fvn = systemPrefixV ++ (show fvn)



readIntAfterPrefix :: String -> String -> Maybe Int
readIntAfterPrefix pre str | pre `isPrefixOf` str   = readMaybe (drop (length pre) str)
                           | otherwise              = Nothing
