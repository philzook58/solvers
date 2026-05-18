{-# LANGUAGE OverloadedStrings #-}
module SMT where

import Data.List as L
import Data.Char
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Map as M
import Text.ParserCombinators.Parsec
import System.IO
import System.Process

data Exp =
    Var T.Text
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
  | FVar T.Text
  deriving Eq

data Command =
    DeclareInt T.Text
  | DeclareBool T.Text
  | Assert Formula
  | AssertSoft Formula
  | CheckSat
  | GetValue [T.Text]

type SMTInput = [Command]

type Model = M.Map T.Text Int

type SMTOutput = Maybe Model

-- Escape/unescape functions for identifiers in SMT solvers.

escape' :: String -> String
escape' []         = []
escape' ('_' : cs) = "__" ++ escape' cs
escape' (c : cs)
  | isAlphaNum c = c : escape' cs
  | otherwise    = "_x" ++ show (fromEnum c) ++ "_" ++ escape' cs

escape :: T.Text -> T.Text
escape s = T.pack ('_': escape' (T.unpack s))

unescape' :: String -> String
unescape' [] = []
unescape' ('_' : 'x' : cs)
  | (s, _ : cs') <- break (== '_') cs = chr (read s :: Int) : unescape' cs'
unescape' "_"             = error "unexpacted end of string"
unescape' ('_': '_' : cs) = '_' : unescape' cs
unescape' ('_': c : _)    = error ("unknown escape code: " ++ [c])
unescape' (c : cs)        = c : unescape' cs

unescape :: String -> T.Text
unescape ('_' : cs) = T.pack (unescape' cs)
unescape s          = error ("unexpected string: " ++ show s)

-- Pretty printers.

tshowApplication :: T.Text -> [T.Text] -> T.Text
tshowApplication s xs =
  "(" <> T.intercalate " " (s : xs) <> ")"

tshowExp :: Exp -> T.Text
tshowExp (Val n)       = T.pack (show n) 
tshowExp (Var x)       = escape x
tshowExp (Plus [])     = "0"
tshowExp (Plus [e])    = tshowExp e
tshowExp (Plus es)     = tshowApplication "+" [ tshowExp e | e <- es ]
tshowExp (Times [])    = "1"
tshowExp (Times [e])   = tshowExp e
tshowExp (Times es)    = tshowApplication "*" [ tshowExp e | e <- es ]
tshowExp (Ite f e1 e2) = "(ite " <> tshowFormula f <> " " <> tshowExp e1 <> " " <> tshowExp e2 <> ")"

tshowFormula :: Formula -> T.Text
tshowFormula (And [])       = "true"
tshowFormula (Or [])        = "false"
tshowFormula (And [f])      = tshowFormula f
tshowFormula (Or [f])       = tshowFormula f
tshowFormula (And fs)       = tshowApplication "and" (L.map tshowFormula fs)
tshowFormula (Or fs)        = tshowApplication "or"  (L.map tshowFormula fs)
tshowFormula (Not f)        = tshowApplication "not" [tshowFormula f]
tshowFormula (Distinct [])  = "true"
tshowFormula (Distinct es)  = tshowApplication "distinct" (L.map tshowExp es)
tshowFormula (Gt e1 e2)     = tshowApplication ">"   (L.map tshowExp [e1,e2])
tshowFormula (Geq e1 e2)    = tshowApplication ">="  (L.map tshowExp [e1,e2])
tshowFormula (Eq e1 e2)     = tshowApplication "="   (L.map tshowExp [e1,e2])
tshowFormula (Iff f1 f2)    = tshowApplication "="   (L.map tshowFormula [f1,f2])
tshowFormula (FVar x)       = escape x

tshowCommand :: Command -> T.Text
tshowCommand (DeclareInt x)  = "(declare-fun " <> escape x <> " () Int)"
tshowCommand (DeclareBool x) = "(declare-fun " <> escape x <> " () Bool)"
tshowCommand (Assert f)      = tshowApplication "assert" [tshowFormula f]
tshowCommand (AssertSoft f)  = tshowApplication "assert-soft" [tshowFormula f]
tshowCommand (CheckSat)      = "(check-sat)"
tshowCommand (GetValue xs)   = "(get-value (" <> T.intercalate " " [ escape x | x <- xs ] <> "))"

tshowSMTInput :: [Command] -> T.Text
tshowSMTInput cs = T.unlines [ tshowCommand c | c <- cs ]

-- Parsing outputs of SMT solvers.

keyword :: String -> Parser ()
keyword s = do
  spaces
  _ <- string s
  spaces

parseVar :: Parser T.Text
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

parsePair :: Parser (T.Text, Int)
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
  return (M.fromList m)

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

top :: Formula
top = And []

bottom :: Formula
bottom = Or []

neg :: Formula -> Formula
neg (Or [])  = And []
neg (And []) = Or []
neg (Not f)  = f
neg f        = Not f

conj :: [Formula] -> Formula
conj fs
  | elem (Or []) fs' = Or []
  | [f] <- fs'       = f
  | otherwise        = And fs'
  where fs' = [ f | f <- fs, f /= And [] ]

disj :: [Formula] -> Formula
disj fs
  | elem (And []) fs' = And []
  | [f] <- fs'        = f
  | otherwise         = Or fs'
  where fs' = [ f | f <- fs, f /= Or [] ]

implies :: Formula -> Formula -> Formula
implies f1 f2 = disj [neg f1, f2]

iff :: Formula -> Formula -> Formula
iff f (And []) = f
iff (And []) f = f
iff f (Or [])  = Not f
iff (Or []) f  = Not f
iff f1      f2 = Iff f1 f2

exactlyOne :: [Formula] -> Formula
-- could be optimized
exactlyOne fs = conj (disj fs : [ disj [neg f1, neg f2] | [f1, f2] <- subsequences fs ])

plus :: [Exp] -> Exp
plus es =
  case es' of
    [] -> Val 0
    [e] -> e
    _   -> Plus es'
  where es' = [ e | e <- es, e /= Val 0 ]

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
ite _ (Val m) (Val n)
  | m == n = Val m
ite f1 (Ite f2 e (Val m)) (Val n)
  | m == n = ite (conj [f1,f2]) e (Val n)
ite f e1 e2 = Ite f e1 e2

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
  | Just n <- M.lookup x a = n
  | otherwise            = 0
evalExp a (Plus es) = sum [ evalExp a e | e <- es ]
evalExp a (Times es) = product [ evalExp a e | e <- es ]
evalExp a (Ite f e1 e2)
  | evalFormula a f = evalExp a e1
  | otherwise       = evalExp a e2

evalFormula :: Model -> Formula -> Bool
evalFormula a (FVar x)      = M.lookup x a /= Just 0
evalFormula a (And fs)      = and [ evalFormula a f | f <- fs ]
evalFormula a (Or fs)       = or [ evalFormula a f | f <- fs ]
evalFormula a (Not f)       = not (evalFormula a f)
evalFormula a (Iff f1 f2)   = evalFormula a f1 == evalFormula a f2
evalFormula a (Distinct es) = distinct [ evalExp a e | e <- es ]
evalFormula a (Eq e1 e2)    = evalExp a e1 == evalExp a e2
evalFormula a (Geq e1 e2)   = evalExp a e1 >= evalExp a e2
evalFormula a (Gt e1 e2)    = evalExp a e1 >  evalExp a e2

-- Functions for expressions and formulas.

vars_exp :: Exp -> S.Set T.Text
vars_exp (Var x)       = S.singleton x
vars_exp (Val _)       = S.empty
vars_exp (Plus es)     = vars_exps es
vars_exp (Times es)    = vars_exps es
vars_exp (Ite f e1 e2) =
  S.unions [vars_formula f, vars_exp e1, vars_exp e2]

vars_exps :: [Exp] -> S.Set T.Text
vars_exps es = S.unions [ vars_exp e | e <- es ]

vars_formula :: Formula -> S.Set T.Text
vars_formula (FVar _)      = S.empty
vars_formula (Distinct es) = vars_exps es
vars_formula (Geq e1 e2)   = vars_exps [e1, e2]
vars_formula (Eq e1 e2)    = vars_exps [e1, e2]
vars_formula (Gt e1 e2)    = vars_exps [e1, e2]
vars_formula (Not f)       = vars_formula f
vars_formula (And fs)      = vars_formulas fs
vars_formula (Or fs)       = vars_formulas fs
vars_formula (Iff f1 f2)   = vars_formulas [f1, f2]

vars_formulas :: [Formula] -> S.Set T.Text
vars_formulas fs = S.unions [ vars_formula f | f <- fs ]

fvars_exp :: Exp -> S.Set T.Text
fvars_exp (Var _)       = S.empty
fvars_exp (Val _)       = S.empty
fvars_exp (Plus es)     = fvars_exps es
fvars_exp (Times es)    = fvars_exps es
fvars_exp (Ite f e1 e2) =
  S.unions [fvars_formula f, fvars_exp e1, fvars_exp e2]

fvars_exps :: [Exp] -> S.Set T.Text
fvars_exps es = S.unions [ fvars_exp e | e <- es ]

fvars_formula :: Formula -> S.Set T.Text
fvars_formula (FVar x)      = S.singleton x
fvars_formula (Distinct es) = fvars_exps es
fvars_formula (Geq e1 e2)   = fvars_exps [e1, e2]
fvars_formula (Eq e1 e2)    = fvars_exps [e1, e2]
fvars_formula (Gt e1 e2)    = fvars_exps [e1, e2]
fvars_formula (Not f)       = fvars_formula f
fvars_formula (And fs)      = fvars_formulas fs
fvars_formula (Or fs)       = fvars_formulas fs
fvars_formula (Iff f1 f2)   = fvars_formulas [f1, f2]

fvars_formulas :: [Formula] -> S.Set T.Text
fvars_formulas fs = S.unions [ fvars_formula f | f <- fs ]

variables :: [Formula] -> ([T.Text], [T.Text])
variables fs = 
  (S.toList (vars_formulas fs),
   S.toList (fvars_formulas fs))

-- Running an SMT solver.

execute :: String -> T.Text -> IO String
execute tool input = do
  (Just hin, Just hout, _, _) <-
    createProcess (proc tool ["/dev/stdin"]) {
      std_in = CreatePipe,
      std_out = CreatePipe }
  TIO.hPutStr hin input
  hClose hin
  hGetContents hout

run :: String -> SMTInput -> IO SMTOutput
run tool input = do
  s <- execute tool (tshowSMTInput input)
  case parse parseSMTOutput "(stdin)" s of
    Left e  -> do
      TIO.putStrLn (tshowSMTInput input)
      putStrLn s
      error (show e)
    Right m -> return m

sat :: String -> Formula -> IO SMTOutput
sat tool f =
  run tool (ints ++ bools ++ [Assert f, CheckSat, GetValue (xs ++ bs)])
  where 
    (xs, bs) = variables [f]
    ints  = [ DeclareInt x | x <- xs ]
    bools = [ DeclareBool b | b <- bs ]

maxsat :: String -> Formula -> [Formula] -> IO SMTOutput
maxsat tool hard softs =
  run tool
    (ints ++ bools ++ Assert hard : 
     [ AssertSoft soft | soft <- softs ] ++ 
     [CheckSat, GetValue (xs ++ bs)])
  where 
    (xs, bs) = variables (hard : softs)
    ints  = [ DeclareInt x | x <- xs ]
    bools = [ DeclareBool b | b <- bs ]

parseAll :: String -> SMTOutput
parseAll s =
  case parse parseSMTOutput "(stdin)" s of
    Left e  -> error (show e)
    Right m -> m
