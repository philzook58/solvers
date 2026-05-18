module ARIParser (readARI) where

import Rules
import Terms
import Text.ParserCombinators.Parsec
import INF

-- intermediate data
data CType = SemiEquational | Join | Oriented
data I = AFun String | ARule CEquation | AQuery [(Term, Term)]

comment :: Parser ()
comment = do
  char ';'
  many (noneOf "\n")
  char '\n'
  return ()

spaces_or_comments :: Parser ()
spaces_or_comments = do
  many ((do { _ <- space; return ()}) <|> comment)
  return ()

number :: Parser Int
number = do
  spaces_or_comments
  ds <- many1 digit
  spaces_or_comments
  return (read ds)

identifier :: Parser String
identifier = do
  spaces_or_comments
  s <- many1 (noneOf " \t\n();:")
  spaces_or_comments
  return s

keyword :: String -> Parser ()
keyword s = do
  _ <- keyword' s
  return ()

keyword' :: String -> Parser String
keyword' s = do
  string s
  spaces_or_comments
  return s

parseS :: Parser a -> Parser a
parseS p = do
  keyword "("
  r <- p
  keyword ")"
  return r

parseCondType :: Parser CType
parseCondType = 
  do { keyword "oriented"; return ARIParser.Oriented } <|>
  do { keyword "join"; return ARIParser.Join } <|>
  do { keyword "semi-equational"; return ARIParser.SemiEquational }

parseFormatType :: Parser CType
parseFormatType =
  do { keyword "TRS"; return ARIParser.Oriented } <|>
  do { keyword "CTRS"; parseCondType }

parseFormat :: Parser CType
parseFormat = do
  keyword "("
  keyword "format"
  c <- parseFormatType
  keyword ":problem"
  keyword "infeasibility"
  keyword ")"
  return c

parseFun :: Parser I
parseFun = do
  keyword "("
  keyword "fun"
  s <- identifier
  _n <- number
  keyword ")"
  return (AFun s)

parseTerm :: [String] -> Parser Term
parseTerm sig = parseApplication sig <|> parseAtom sig

parseAtom :: [String] -> Parser Term
parseAtom sig = do
  s <- identifier
  if elem s sig 
    then return (F s [])
    else return (V s)

parseApplication :: [String] -> Parser Term
parseApplication sig = do
  keyword "("
  f <- identifier
  ts <- many1 (parseTerm sig)
  keyword ")"
  return (F f ts)

parseCond :: [String] -> Parser (Term, Term)
parseCond sig = do
  keyword "("
  keyword "="
  l <- parseTerm sig
  r <- parseTerm sig
  keyword ")"
  return (l, r)

parseRule :: [String] -> Parser I
parseRule sig = do
  keyword "("
  keyword "rule"
  l <- parseTerm sig
  r <- parseTerm sig
  cs <- many (parseCond sig)
  keyword ")"
  return (ARule (cs, (l, r)))

parseInfeasible :: [String] -> Parser I
parseInfeasible sig = do
  keyword "("
  keyword "infeasible?"
  cs <- many1 (parseCond sig)
  keyword ")"
  return (AQuery cs)

parseARI :: Parser INFProblem
parseARI = do
  spaces_or_comments
  ctype <- parseFormat
  (trs, qs) <- parseARI' [] [] []
  case ctype of
    ARIParser.SemiEquational -> return (INF.SemiEquational (trs, qs))
    ARIParser.Join -> return (INF.Join (trs, qs))
    ARIParser.Oriented -> return (INF.Oriented (trs, qs))
  where
    parseARI' sig trs queries = do
      r <- try parseFun <|> try (parseRule sig) <|> parseInfeasible sig
      case r of
        AFun f -> parseARI' (f : sig) trs queries
        ARule rule -> parseARI' sig (rule : trs) queries
        AQuery qs -> do { spaces_or_comments; return (trs, qs)}

readARI :: String -> IO (Either ParseError INFProblem)
readARI path = do
  s <- readFile path
  let r = parse parseARI "(readARI)" s
  return r
