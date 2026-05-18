{-# LANGUAGE OverloadedStrings #-}
module TPTP where

-- NOTE: the BNF is provided at https://tptp.org/TPTP/SyntaxBNF.html
-- currently only UEQ is supported

import Prelude hiding (negate)
import Text.ParserCombinators.Parsec
import System.Directory
import System.FilePath (normalise, takeFileName)
import qualified Data.Text as T
import qualified Data.Map as M
import Data.Char (isAlphaNum, isLower)

import Parsing

data Relation = Eq | Neq

type Formula = (Relation, (Term, Term))

type AnnotatedFormula = (String, String, String, Formula) -- (filename, name_of_formula, role, formula)

data Declaration = CNF AnnotatedFormula | Include String

type Annotation = (T.Text, T.Text, T.Text) -- (filename, name_of_formula, role)

type AnnotatedEquation = ((Term, Term), Maybe Annotation) -- equations introduced by encoding have no annotation.

data EncodingInfo = EncodingInfo {
  _eq :: T.Text,
  _true :: T.Text,
  _false :: T.Text,
  _original_goal :: AnnotatedEquation
}

-- Manipilation functions

negate :: Formula -> Formula
negate (Eq,  e) = (Neq, e)
negate (Neq, e) = (Eq,  e)

-- Waldmeister's preprocessing.
-- Given a set E of axioms and a non-ground goal s = t,
-- add eq(X, X) = true and eq(s, t) = false to E and
-- change the goal to true = false.
waldmeister :: Signature -> [AnnotatedEquation] -> AnnotatedEquation -> (Signature, [AnnotatedEquation], AnnotatedEquation, EncodingInfo)
waldmeister sig axs g@((s, t), _) =  (sig', eq1 : eq2 : axs, goal, info)
  where
    eq = fresh sig "eq"
    true = fresh sig "true"
    false = fresh sig "false"
    sig' = M.insert false 0 (M.insert true 0 (M.insert eq 2 sig))
    eq1 = ((F eq [ V "X", V "X" ], F true []), Nothing)
    eq2 = ((F eq [ s, t ], F false []), Nothing)
    goal = ((F true [], F false []), Nothing)
    info = EncodingInfo {
      _eq = eq,
      _true = true,
      _false = false,
      _original_goal = g
    }

-- output: (sig, es, goal, info)
preprocess :: [AnnotatedFormula] -> Maybe (Signature, [AnnotatedEquation], AnnotatedEquation, Maybe EncodingInfo)
preprocess fs = case negatives of
  g@((s, t), _) : _ -> -- only first goal is considered
    if ground s && ground t
      then return (sig, positives, g, Nothing)
      else let (sig', axs, g', info) = waldmeister sig positives g
           in return (sig', axs, g', Just info)
  [] -> Nothing
  where
    positives = [ ((l, r), Just (T.pack fname, T.pack name', T.pack role)) | (fname, name', role, (TPTP.Eq, (l, r))) <- fs ] 
    negatives = [ ((l, r), Just (T.pack fname, T.pack name', T.pack role)) | (fname, name', role, (TPTP.Neq, (l, r))) <- fs ]
    sig = signatureOf [ t | (_, _, _, (_, (l, r))) <- fs, t <- [l, r] ]

tshowAnnotation :: Annotation -> T.Text
tshowAnnotation (_, nam, _) = nam 

tshowAnnotatedEquation :: AnnotatedEquation -> T.Text
tshowAnnotatedEquation ((l, r), Just info) = "(" <> tshowAnnotation info <> ") " <> tshow l <> " = " <> tshow r
tshowAnnotatedEquation ((l, r), Nothing) = "(*) " <> tshow l <> " = " <> tshow r

tshowProblem :: [AnnotatedEquation] -> AnnotatedEquation -> T.Text
tshowProblem es goal =
  "axioms:\n" <>
  T.unlines [ tshowAnnotatedEquation e | e <- es ] <> 
  "goal:\n" <> tshowAnnotatedEquation goal 

-- quote for printing

quote :: T.Text -> T.Text
quote x
  | isValid x = x
  | otherwise = "\'" <> escape x <> "\'"

isValid :: T.Text -> Bool
isValid t = case T.uncons t of
  Just (c, rest) -> isLower c && T.all (\ch -> isAlphaNum ch || ch == '_') rest
  Nothing        -> False

escape :: T.Text -> T.Text
escape = T.concatMap escapeChar
  where
    escapeChar '\''  = "\\\'"
    escapeChar '\\' = "\\\\"
    escapeChar c    = T.singleton c

showTerm :: Term -> T.Text
showTerm (V x) = x
showTerm (F f []) = quote f
showTerm (F f ts) = quote f <> "(" <> T.intercalate ", " [ showTerm t | t <- ts ] <> ")"

-- Tokenizers

name :: Parser String
name = try atomic_word <|> integer

atomic_word :: Parser String
atomic_word = try lower_word <|> single_quoted

integer :: Parser String
integer = many1 digit

alpha_numeric :: Parser Char
alpha_numeric = try alphaNum <|> char '_'

lower_word :: Parser String
lower_word = do
  _ <- spaces_or_comments
  c <- lower
  s <- many alpha_numeric
  _ <- spaces_or_comments
  return (c : s)

upper_word :: Parser String
upper_word = do
  spaces_or_comments
  c <- upper
  s <- many alpha_numeric
  spaces_or_comments
  return (c : s)

single_quoted :: Parser String
single_quoted = do
  spaces_or_comments
  _ <- char '\''
  s <- many char_in_single_quote
  _ <- char '\''
  spaces_or_comments
  return s

char_in_single_quote :: Parser Char
char_in_single_quote = try escaped_char_in_single_quote <|> noneOf "\\'"

escaped_char_in_single_quote :: Parser Char
escaped_char_in_single_quote = do
  _ <- char '\\'
  c <- oneOf "\\'"
  return c

comment :: Parser ()
comment = do
  _ <- char '%'
  _ <- many (noneOf "\n")
  _ <- char '\n'
  return ()

spaces_or_comments :: Parser ()
spaces_or_comments = do
  _ <- many (try (do { _ <- space; return () }) <|> comment)
  return ()

keyword :: String -> Parser ()
keyword s = do
  spaces_or_comments
  _ <- string s
  spaces_or_comments
  return () 

paren :: Parser a -> Parser a
paren p = do
  keyword "("
  x <- p
  keyword ")"
  return x

-- Parsers for terms and formulas.

parseTerm :: Parser Term
parseTerm = try parseVariable <|> try parseFunctionApplication <|> parseConstant 

parseVariable :: Parser Term
parseVariable = do
  s <- upper_word
  return (V (T.pack s))

constant :: Parser String
constant = functor

functor :: Parser String
functor = atomic_word

parseConstant :: Parser Term
parseConstant = do
  s <- constant
  return (F (T.pack s) [])

parseFunctionApplication :: Parser Term
parseFunctionApplication = do
  f <- functor
  ts <- paren (sepBy parseTerm (keyword ","))
  return (F (T.pack f) ts)

parseEq :: Parser Relation
parseEq = do
  keyword "="
  return Eq

parseNeq :: Parser Relation
parseNeq = do
  keyword "!="
  return Neq

parseRelation :: Parser Relation
parseRelation = try parseEq <|> parseNeq

parseAtom :: Parser Formula
parseAtom = do
  s <- parseTerm
  r <- parseRelation
  t <- parseTerm
  return (r, (s, t))

parseNegativeLiteral :: Parser Formula
parseNegativeLiteral = do
  keyword "~"
  f <- parseAtom 
  return (negate f)

parseLiteral :: Parser Formula
parseLiteral = try parseNegativeLiteral <|> parseAtom

parseFormula :: Parser Formula
parseFormula = try (paren parseFormula) <|> parseLiteral

-- Parsers for declarations.

parseCNF :: String -> Parser Declaration
parseCNF fname = do
  keyword "cnf"; keyword "("
  clauseName <- name
  keyword ","
  role <- lower_word
  keyword ","
  formula <- parseFormula
  keyword ")"
  keyword "."
  return (CNF (takeFileName fname, clauseName, role, formula))

parseInclude :: Parser Declaration
parseInclude = do
  keyword "include"
  keyword "("
  filename <- single_quoted
  keyword ")"
  keyword "."
  return (Include filename)

parseDeclaration :: String -> Parser Declaration
parseDeclaration fname = try (parseCNF fname) <|> parseInclude

parseToplevel :: String -> Parser [Declaration]
parseToplevel fname = do
  ds <- many (parseDeclaration fname)
  eof
  return ds

-- Reading files.

lookupFile :: String -> [String] -> IO (Maybe String)
lookupFile filename [] = do
  b <- doesFileExist filename -- interprete as absolute path
  if b
    then return (Just filename)
    else return Nothing
lookupFile filename (dir : dirs) = do
  let path = dir ++ "/" ++ filename
  b <- doesFileExist path
  if b 
    then return (Just path)
    else lookupFile filename dirs

readTPTP :: [String] -> String -> IO [AnnotatedFormula]
readTPTP dirs filename = do
  m <- lookupFile filename dirs
  case m of
    Nothing -> error ("File not found: " ++ filename)
    Just path -> do
      result <- parseFromFile (parseToplevel (normalise path)) path
      case result of
        Left e -> error (show e)
        Right declarations -> readTPTP' declarations
  where
    readTPTP' [] = return []
    readTPTP' (CNF af : ds) = do
      result <- readTPTP' ds
      return (af : result)
    readTPTP' (Include path : ds) = do
      afs1 <- readTPTP dirs path
      afs2 <- readTPTP' ds
      return (afs1 ++ afs2)
