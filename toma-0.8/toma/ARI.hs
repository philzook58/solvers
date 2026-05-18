module ARI where

import Text.ParserCombinators.Parsec -- TODO: replace with megaparsec
import qualified Data.Text as T
import qualified Data.Map as M
import Data.Maybe

import Parsing

type CRule = ((Term, Term), [(Term, Term)]) -- conditional rule
type Query = (Term, Term)

-- Scanners

comment :: Parser ()
comment = do
  _ <- char ';'
  skipMany (noneOf "\n")

whitespaces :: Parser ()
whitespaces = skipMany (do { _ <- space; return () } <|> comment)

simple_identifier :: Parser T.Text
simple_identifier = do
  whitespaces
  s <- many1 (noneOf "|(); \t\r\n")
  whitespaces
  return (T.pack s)

quoted_identifier :: Parser T.Text
quoted_identifier = do
  whitespaces
  _ <- char '|'
  s <- many1 (noneOf "| \t\r\n")
  _ <- char '|'
  whitespaces
  return (T.pack "|" <> T.pack s <> T.pack "|")

identifier :: Parser T.Text
identifier = try simple_identifier <|> quoted_identifier

number :: Parser Int
number = do
  whitespaces
  s <- many1 digit
  whitespaces
  return (read s :: Int)

keyword :: String -> Parser ()
keyword s = do
  whitespaces
  _ <- string s
  whitespaces

param :: String -> a -> Parser a
param s x = do
  keyword s
  return x
            
-- Parsing functions.

parse_cond_type :: Parser ()
parse_cond_type = keyword "oriented" <|> keyword "join" <|> keyword "semi-equational"

parse_format_type :: Parser ()
parse_format_type =
  keyword "TRS" <|> do { keyword "CTRS"; parse_cond_type }

parse_problem_type :: Parser ()
parse_problem_type = do
  keyword ":problem"
  keyword "infeasibility"

parse_format :: Parser ()
parse_format = do
  keyword "("
  keyword "format"
  parse_format_type
  optional parse_problem_type
  keyword ")"

parse_fun :: Parser (T.Text, Int)
parse_fun = do
  keyword "("
  keyword "fun"
  f <- identifier
  n <- number
  keyword ")"
  return (f, n)

parse_term :: Signature -> Parser Term
parse_term sig = 
  try (parse_variable_or_constant sig) <|> 
  parse_function sig

parse_variable_or_constant :: Signature -> Parser Term
parse_variable_or_constant sig = do
  x <- identifier
  case M.lookup x sig of
    Nothing -> return (V x)
    Just 0  -> return (F x [])
    Just _  -> error (show x ++ " is not a constant.")

parse_function :: Signature -> Parser Term
parse_function sig = do
  keyword "("
  f <- identifier
  ts <- many (parse_term sig)
  keyword ")"
  case M.lookup f sig of
    Nothing            -> error (show f ++ " is not declared")
    Just n | m == n    -> return (F f ts)
           | m < n     -> error (show f ++ " takes too few arguemnts")
           | otherwise -> error (show f ++ " takes too many arguments")
      where m = length ts

parse_condition :: Signature -> Parser (Term, Term)
parse_condition sig = do
  keyword "("
  keyword "="
  l <- parse_term sig
  r <- parse_term sig
  keyword ")" 
  return (l, r)

parse_rule :: Signature -> Parser CRule
parse_rule sig = do
  keyword "("
  keyword "rule"
  l <- parse_term sig
  r <- parse_term sig
  cs <- many (parse_condition sig)
  keyword ")"
  return ((l, r), cs)

parse_query :: Signature -> Parser [Query]
parse_query sig = do
  keyword "("
  keyword "infeasible?"
  cs <- many1 (parse_condition sig)
  keyword ")"
  return cs

parse_ari :: Parser (Signature, [CRule], Maybe [Query])
parse_ari = do
  parse_format
  sig' <- many (try parse_fun)
  let sig = M.fromList sig'
  rules <- many (try (parse_rule sig))
  m <- optionMaybe (parse_query sig)
  eof
  return (sig, rules, m)

readFile :: FilePath -> IO (Signature, [CRule], Maybe [Query])
readFile f = do
  input <- Prelude.readFile f
  case parse parse_ari f input of
    Left err -> error (show err)
    Right r -> return r

readINF :: FilePath -> IO (Signature, [CRule], [Query])
readINF f = do
  (sig, crules, m) <- ARI.readFile f
  case m of
    Just qs -> return (sig, crules, qs)
    Nothing -> error "query is not provided"

readTRS :: FilePath -> IO (Signature, [(Term, Term)])
readTRS f = do
  (sig, crules, m) <- ARI.readFile f
  if (all (\(_, cs) -> Prelude.null cs) crules && isNothing m)
    then return (sig, map fst crules)
    else error "input is not plain TRS"
