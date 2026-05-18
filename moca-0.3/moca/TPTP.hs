module TPTP (Atom (..), Literal, Clause, TPTPInput (..), TPTP,
             readTPTP, showTPTP) where

import System.Directory
import Data.List
import Terms
import Text.ParserCombinators.Parsec
import Debug.Trace


data Atom = Predicate Term | Equation Term Term

type Literal = (Bool, Atom)

type Clause = [Literal]

data TPTPInput = CNF String String Clause | Include String

type TPTP = [TPTPInput]


-- Pretty printers

instance Show Atom where
  show (Predicate t)  = show t
  show (Equation s t) = show s ++ " = " ++ show t

showLiteral :: Literal -> String
showLiteral (True,  Equation l r) = "(" ++ show l ++ " = "  ++ show r ++ ")"
showLiteral (False, Equation l r) = "(" ++ show l ++ " != " ++ show r ++ ")"
showLiteral (True,  Predicate t)  = show t
showLiteral (False, Predicate t)  = "~ " ++ show t

showClause literals = intercalate " | " [ showLiteral l | l <- literals ]

instance Show TPTPInput where
  show (CNF name role clause) =
    "cnf(" ++ name ++ ", " ++ role ++ ", " ++
    showClause clause ++ ")."
  show (Include path) = "include(" ++ singleQuote path ++")."

singleQuote s = "'" ++ singleQuote1 s ++ "'"
singleQuote1 []         = []
singleQuote1 ('\'' : s) = "\\'"  ++ singleQuote1 s
singleQuote1 ('\\' : s) = "\\\\" ++ singleQuote1 s
singleQuote1 (c    : s) = c : singleQuote1 s

showTPTP :: TPTP -> String
showTPTP tptp = unlines [ show t | t <- tptp ]


-- Tokenizers

name :: Parser String
name = try atomic_word <|> integer

atomic_word :: Parser String
atomic_word = try lower_word <|> single_quoted

integer :: Parser String
integer = many1 digit

alpha_numeric = try alphaNum <|> char '_'

lower_word :: Parser String
lower_word = do
  spaces_or_comments
  c <- lower
  s <- many alpha_numeric
  spaces_or_comments
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
  char '\''
  s <- many char_in_single_quote
  char '\''
  spaces_or_comments
  return s

char_in_single_quote :: Parser Char
char_in_single_quote = try escaped_char_in_single_quote <|> noneOf "\\'"

escaped_char_in_single_quote :: Parser Char
escaped_char_in_single_quote = do
  char '\\'
  c <- oneOf "\\'"
  return c

comment = do
  char '%'
  many (noneOf "\n")
  char '\n'

spaces_or_comments = many (try space <|> comment)

keyword :: String -> Parser ()
keyword s = do
  spaces_or_comments
  string s
  spaces_or_comments
  return () 

paren :: Parser a -> Parser a
paren p = do
  keyword "("
  x <- p
  keyword ")"
  return x


-- Parsers

tptp_file :: Parser [TPTPInput]
tptp_file = do
  as <- many tptp_input
  eof
  return as

tptp_input :: Parser TPTPInput
tptp_input = try annotated_formula <|> include

include :: Parser TPTPInput
include = do
  keyword "include"
  keyword "("
  file <- single_quoted
  keyword ")"
  keyword "."
  return (Include file)

annotated_formula :: Parser TPTPInput
annotated_formula = cnf_annotated
  
cnf_annotated :: Parser TPTPInput
cnf_annotated = do
  keyword "cnf"; keyword "("
  s <- name
  keyword ","
  r <- lower_word
  keyword ","
  c <- cnf_formula
  keyword ")"
  keyword "."
  return (CNF s r c)

cnf_formula :: Parser Clause
cnf_formula = try (paren disjunction) <|> disjunction

disjunction :: Parser Clause
disjunction = sepBy1 literal (keyword "|") 

literal :: Parser Literal
literal = try negative_literal <|> positive_literal

negative_literal :: Parser Literal
negative_literal = do
  keyword "~"
  (b, l) <- positive_literal 
  return (not b, l)

positive_literal :: Parser Literal
positive_literal = try fof_infix_unary <|> fof_atomic_formula

fof_atomic_formula :: Parser Literal
fof_atomic_formula = do
  t <- fof_term
  return (True, Predicate t)

fof_infix_unary :: Parser Literal
fof_infix_unary = do
  l <- fof_term
  b <- infix_relation
  r <- fof_term
  return (b, Equation l r)

infix_relation :: Parser Bool
infix_relation = try infix_eq <|> infix_neq

infix_eq :: Parser Bool
infix_eq = do
  keyword "="
  return True
  
infix_neq :: Parser Bool
infix_neq = do
  keyword "!="
  return False

fof_term :: Parser Term
fof_term = try variable <|> try function_application <|> constant 

variable :: Parser Term
variable = do
  s <- upper_word
  return (V s)

constant :: Parser Term
constant = do
  s <- lower_word
  return (F s [])

function_application :: Parser Term
function_application = do
  f <- lower_word
  ts <- paren (sepBy fof_term (keyword ","))
  return (F f ts)


-- Reader

readTPTP :: [String] -> String -> IO (Either ParseError TPTP)
readTPTP dirs path = do
  result <- parseFromFile tptp_file path
  case result of
    Left e     -> return (Left e)
    Right tptp -> includeTPTP dirs tptp

includeTPTP :: [String] -> TPTP -> IO (Either ParseError TPTP)
includeTPTP _ [] = return (Right [])
includeTPTP dirs (tptpInput : tptp) = do
  result1 <- includeTPTPInput dirs tptpInput
  case result1 of
    Left e      -> return (Left e)
    Right tptp1 -> do
      result2 <- includeTPTP dirs tptp
      case result2 of
        Left e      -> return (Left e)
        Right tptp2 -> return (Right (tptp1 ++ tptp2))


includeTPTPInput :: [String] -> TPTPInput -> IO (Either ParseError TPTP)
includeTPTPInput dirs (Include path) = do
  mbpath <- existingPath dirs path
  case mbpath of 
    Nothing -> error ("cannot open file "++ path)
    Just path' -> readTPTP dirs path'
includeTPTPInput _ x = return (Right [x])

existingPath :: [String] -> String -> IO (Maybe String)
existingPath           [] path = return Nothing
existingPath (dir : dirs) path = do
  let path' = (dir ++ "/" ++ path)
  b <- doesFileExist path'
  if b then return (Just path')
       else existingPath dirs path
