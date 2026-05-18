module SMT where

import Data.List
import Data.Char
import Data.Either
import Text.ParserCombinators.Parsec
import System.IO
import System.Process

data Exp =
    Var String
  | Val Int
  | Plus [Exp]
  | Times [Exp]
  | Ite Formula Exp Exp
  deriving Eq

data Formula =
    And [Formula]
  | Or [Formula]
  | Not Formula
  | Distinct [Exp]
  | Geq Exp Exp
  | Gt Exp Exp
  | Eq Exp Exp
  | Iff Formula Formula
  | FVar String
  deriving Eq

data Command =
    DeclareInt String
  | DeclareBool String
  | Assert Formula
  | AssertSoft Formula
  | CheckSat
  | GetValue [String]

type SMTInput = [Command]

type Model = [(String, Int)]

type SMTOutput = Maybe Model

-- Escape/unescape functions for identifiers in SMT solvers.

escape' :: String -> String
escape' []         = []
escape' ('_' : cs) = "__" ++ escape' cs
escape' (c : cs)
  | isAlphaNum c = c : escape' cs
  | otherwise    = "_x" ++ show (fromEnum c) ++ "_" ++ escape' cs

escape :: String -> String
escape s = '_': escape' s

unescape' :: String -> String
unescape' [] = []
unescape' ('_' : 'x' : cs)
  | (s, _ : cs') <- break (== '_') cs = chr (read s :: Int) : unescape' cs'
unescape' "_"             = error "unexpacted end of string"
unescape' ('_': '_' : cs) = '_' : unescape' cs
unescape' ('_': c : _)    = error ("unknown escape code: " ++ [c])
unescape' (c : cs)        = c : unescape' cs

unescape :: String -> String
unescape ('_' : cs) = unescape' cs
unescape s          = error ("unexpected string: " ++ show s)

-- Pretty printers.

showApplication :: Show a => String -> [a] -> String
showApplication s xs =
  "(" ++ intercalate " " (s : [ show x | x <- xs ]) ++ ")"

instance Show Exp where
  show (Val n)       = show n
  show (Var x)       = escape x
  show (Plus [])     = "0"
  show (Plus [e])    = show e
  show (Plus es)     = showApplication "+" es
  show (Times [])    = "1"
  show (Times [e])   = show e
  show (Times es)    = showApplication "*" es
  show (Ite f e1 e2) = "(ite " ++ show f ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"

instance Show Formula where
  show (And [])       = "true"
  show (Or [])        = "false"
  show (And [f])      = show f
  show (Or [f])       = show f
  show (And fs)       = showApplication "and" fs
  show (Or fs)        = showApplication "or"  fs
  show (Not f)        = showApplication "not" [f]
  show (Distinct [])  = "true"
  show (Distinct es)  = showApplication "distinct" es
  show (Gt e1 e2)     = showApplication ">"   [e1,e2]
  show (Geq e1 e2)    = showApplication ">="  [e1,e2]
  show (Eq e1 e2)     = showApplication "="   [e1,e2]
  show (Iff f1 f2)    = showApplication "="   [f1,f2]
  show (FVar x)       = escape x

instance Show Command where
  show (DeclareInt x)  = "(declare-fun " ++ escape x ++ " () Int)"
  show (DeclareBool x) = "(declare-fun " ++ escape x ++ " () Bool)"
  show (Assert f)      = showApplication "assert" [f]
  show (AssertSoft f)  = showApplication "assert-soft" [f]
  show (CheckSat)      = "(check-sat)"
  show (GetValue xs)   = "(get-value (" ++ intercalate " " [ escape x | x <- xs ] ++ "))"

showSMTInput :: [Command] -> String
showSMTInput cs = unlines [ show c | c <- cs ]


-- Parsing outputs of SMT solvers.

keyword :: String -> Parser ()
keyword s = do
  spaces
  _ <- string s
  spaces

parseVar :: Parser String
parseVar = do
  spaces
  s <- many1 (noneOf " \n\r\t\0,()")
  spaces
  return (unescape s)

parseNegative :: Parser Int
parseNegative = do
  keyword "("
  keyword "-"
  t <- many1 digit
  keyword ")"
  return (- (read t :: Int))

parseNonnegative :: Parser Int
parseNonnegative = do
  spaces
  t <- many1 digit
  spaces
  return (read t :: Int)

parseInt :: Parser Int
parseInt = do
  i <- parseNegative <|> parseNonnegative
  return i

parseTrue :: Parser Int
parseTrue = do
  keyword "true"
  return 1

parseFalse :: Parser Int
parseFalse = do
  keyword "false"
  return 0

parseBool :: Parser Int
parseBool = parseTrue <|> parseFalse

parseValue :: Parser Int
parseValue = try parseBool <|> try parseInt

parsePair :: Parser (String, Int)
parsePair = do
  keyword "("
  x <- parseVar
  y <- parseValue
  keyword ")"
  return (x, y)

parseModel :: Parser Model
parseModel = do
  keyword "("
  m <- many parsePair
  keyword ")"
  return m

parseSat :: Parser SMTOutput
parseSat = do
  keyword "sat"
  m <- parseModel
  return (Just m)

parseUnsat :: Parser SMTOutput
parseUnsat = do
  keyword "unsat"
  return Nothing

parseSMTOutput :: Parser SMTOutput
parseSMTOutput = try parseSat <|> parseUnsat

-- Constructors.

plus' :: [Exp] -> [Exp]
plus' []              = []
plus' (Val 0 : es)    = plus' es
plus' (Plus es' : es) = plus' (es' ++ es)
plus' (e : es)        = e : plus' es

plus :: [Exp] -> Exp
plus es =
  case plus' es of
    []  -> Val 0
    es' -> Plus es' 

top :: Formula
top = And []

bottom :: Formula
bottom = Or []

formula :: Bool -> Formula
formula True  = top
formula False = bottom

neg :: Formula -> Formula
neg (Or [])  = And []
neg (And []) = Or []
neg (Not f)  = f
neg f        = Not f

conj' :: [Formula] -> [Formula] -> Formula
conj' [f] []              = f
conj' fs []               = And fs
conj' fs (And fs' : fs'') = conj' fs (fs' ++ fs'')
conj' _  (Or [] : _)      = bottom
conj' fs (f : fs')        = conj' (f : fs) fs'

conj :: [Formula] -> Formula
conj fs = conj' [] fs

disj' :: [Formula] -> [Formula] -> Formula
disj' [f] []             = f
disj' fs []              = Or fs
disj' fs (Or fs' : fs'') = disj' fs (fs' ++ fs'')
disj' _  (And [] : _)    = top
disj' fs (f : fs')       = disj' (f : fs) fs'

disj :: [Formula] -> Formula
disj fs = disj' [] fs

implies :: Formula -> Formula -> Formula
implies f g = disj [neg f, g]

iff :: Formula -> Formula -> Formula
iff f (And []) = f
iff (And []) f = f
iff f (Or [])  = neg f
iff (Or []) f  = neg f
iff f1      f2 = Iff f1 f2

boolToFormula :: Bool -> Formula
boolToFormula True  = And []
boolToFormula False = Or []

eq :: Exp -> Exp -> Formula
eq (Val m) (Val n) = boolToFormula (m == n)
eq e1      e2      = Eq e1 e2

geq :: Exp -> Exp -> Formula
geq (Val m) (Val n) = boolToFormula (m >= n)
geq e1      e2      = Geq e1 e2

gt :: Exp -> Exp -> Formula
gt (Val m) (Val n) = boolToFormula (m > n)
gt e1      e2      = Gt e1 e2

ite :: Formula -> Exp -> Exp -> Exp
ite (And []) e _ = e
ite (Or  []) _ e = e
ite f1 (Ite f2 e11 e12) e2
  | e12 == e2    = ite (conj [f1, f2]) e11 e2
ite f e1 e2      = Ite f e1 e2

times01 :: Formula -> Exp -> Exp
times01 f e = ite f e (Val 0)

-- Queries

sizeExp :: Exp -> Int
sizeExp (Val _)       = 1
sizeExp (Var _)       = 1
sizeExp (Plus es)     = 1 + sum [ sizeExp e | e <- es ]
sizeExp (Times es)    = 1 + sum [ sizeExp e | e <- es ]
sizeExp (Ite f e1 e2) = 1 + sizeFormula f + sizeExp e1 + sizeExp e2

sizeFormula :: Formula -> Int
sizeFormula (FVar _)      = 1
sizeFormula (Not f)       = 1 + sizeFormula f
sizeFormula (And fs)      = 1 + sum [ sizeFormula f | f <- fs ]
sizeFormula (Or  fs)      = 1 + sum [ sizeFormula f | f <- fs ]
sizeFormula (Iff e1 e2)   = 1 + sizeFormula e1 + sizeFormula e2
sizeFormula (Distinct es) = 1 + sum [ sizeExp e | e <- es ]
sizeFormula (Eq  e1 e2)   = 1 + sizeExp e1 + sizeExp e2
sizeFormula (Geq e1 e2)   = 1 + sizeExp e1 + sizeExp e2
sizeFormula (Gt  e1 e2)   = 1 + sizeExp e1 + sizeExp e2

-- Evaluation functions.

distinct :: Eq a => [a] -> Bool
distinct []       = True
distinct (x : xs) = all (/= x) xs && distinct xs

evalExp :: Model -> Exp -> Int
evalExp _ (Val n) = n
evalExp a (Var x)
  | Just n <- lookup x a = n
  | otherwise            = 0
evalExp a (Plus es) = sum [ evalExp a e | e <- es ]
evalExp a (Times es) = product [ evalExp a e | e <- es ]
evalExp a (Ite f e1 e2)
  | evalFormula a f = evalExp a e1
  | otherwise       = evalExp a e2

evalFormula :: Model -> Formula -> Bool
evalFormula a (FVar x)      = lookup x a /= Just 0
evalFormula a (And fs)      = and [ evalFormula a f | f <- fs ]
evalFormula a (Or fs)       = or [ evalFormula a f | f <- fs ]
evalFormula a (Not f)       = not (evalFormula a f)
evalFormula a (Iff f1 f2)   = evalFormula a f1 == evalFormula a f2
evalFormula a (Distinct es) = distinct [ evalExp a e | e <- es ]
evalFormula a (Eq e1 e2)    = evalExp a e1 == evalExp a e2
evalFormula a (Geq e1 e2)   = evalExp a e1 >= evalExp a e2
evalFormula a (Gt e1 e2)    = evalExp a e1 >  evalExp a e2

-- Functions for expressions and formulas.

variablesInExp :: Exp -> [Either String String]
variablesInExp (Var x)       = [Left x]
variablesInExp (Val _)       = []
variablesInExp (Plus es)     = variablesInExps es
variablesInExp (Times es)    = variablesInExps es
variablesInExp (Ite f e1 e2) =
  nub (variablesInFormula f ++ variablesInExp e1 ++ variablesInExp e2)

variablesInExps :: [Exp] -> [Either String String]
variablesInExps es = nub [ x | e <- es, x <- variablesInExp e ]

variablesInFormula :: Formula -> [Either String String]
variablesInFormula (FVar x)      = [Right x]
variablesInFormula (Distinct es) = variablesInExps es
variablesInFormula (Geq e1 e2)   = variablesInExps [e1, e2]
variablesInFormula (Eq e1 e2)    = variablesInExps [e1, e2]
variablesInFormula (Gt e1 e2)    = variablesInExps [e1, e2]
variablesInFormula (Not f)       = variablesInFormula f
variablesInFormula (And fs)      = variablesInFormulas fs
variablesInFormula (Or fs)       = variablesInFormulas fs
variablesInFormula (Iff f1 f2)   = variablesInFormulas [f1, f2]

variablesInFormulas :: [Formula] -> [Either String String]
variablesInFormulas fs = nub [ x | f <- fs, x <- variablesInFormula f ]

variables :: Formula -> ([String], [String])
variables f = partitionEithers (variablesInFormula f)

-- Running an SMT solver.

execute :: String -> String -> IO String
execute tool input = do
  (Just hin, Just hout, _, _) <-
    createProcess (proc tool ["/dev/stdin"]) {
      std_in = CreatePipe,
      std_out = CreatePipe }
  hPutStr hin input
  hClose hin
  hGetContents hout

run :: String -> SMTInput -> IO SMTOutput
run tool input = do
  -- putStrLn ("-- SMT input --\n" ++ showSMTInput input ++ "\n")
  s <- execute tool (showSMTInput input)
  -- putStrLn ("-- SMT output --\n" ++ s ++ "\n")
  case parse parseSMTOutput "(stdin)" s of
    Left e  -> do
      putStrLn (showSMTInput input)
      putStrLn s
      error (show e)
    Right m -> return m

sat :: String -> Formula -> IO SMTOutput
sat tool f =
  run tool (ints ++ bools ++ [Assert f, CheckSat, GetValue (xs ++ bs)])
  where 
    (xs, bs) = variables f
    ints  = [ DeclareInt x | x <- xs ]
    bools = [ DeclareBool b | b <- bs ]

maxsat :: String -> Formula -> [Formula] -> IO SMTOutput
maxsat tool hard softs =
  run tool (ints ++ bools ++ asserts ++ avoidBug ++ 
            [CheckSat, GetValue ("xxxx" : xs ++ bs)])
  where
    (xs, bs) = variables (And (hard : softs))
    ints  = [ DeclareInt x | x <- xs ]
    bools = [ DeclareBool b | b <- bs ]
    avoidBug = [ DeclareInt "xxxx", Assert (Gt (Var "xxxx") (Val 0)) ]
    asserts = Assert hard : [ AssertSoft f | f <- softs ]


parseAll :: String -> SMTOutput
parseAll s =
  case parse parseSMTOutput "(stdin)" s of
    Left e  -> error (show e)
    Right m -> m
