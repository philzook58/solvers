module Parser 
  (Spec (..),
   readTerm, readRule, readTRS, readSpec, readSpecFile) where

import Data.List (intercalate)
import Term
import Rule
import TRS
import Text.ParserCombinators.Parsec

data Spec = Spec {
  _VAR :: [String],
  _RULES :: TRS
}

-- Pretty printers.

showVAR :: Spec -> String
showVAR spec =
  "(VAR " ++ intercalate " " (_VAR spec) ++ ")\n"

showRULES :: Spec -> String
showRULES spec =
  "(RULES\n" ++ 
  unlines [ "  " ++ showRule rule | rule <- _RULES spec ] ++ 
  ")\n"

instance Show Spec where
  show spec = 
    showVAR spec ++
    showRULES spec

-- auxiliary functions

convertTRS :: [String] -> TRS -> TRS    
convertTRS xs trs = TRS.substitute trs sigma
    where sigma = [ (x, F x []) | x <- TRS.variables trs, not (elem x xs) ]
        
-- Scanners

identifier :: Parser String
identifier = do
  spaces
  x <- many1 (noneOf "(), \t\r\n")
  spaces
  return x

keyword :: String -> Parser ()
keyword s = do
  spaces
  _ <- string s
  spaces
  return ()
            
parseTerm :: Parser Term
parseTerm = try parseFunction <|> parseVariable

parseVariable :: Parser Term
parseVariable = do
  x <- identifier
  return (V x)

parseFunction :: Parser Term
parseFunction = do
  f <- identifier
  keyword "("
  t <- sepBy parseTerm (keyword ",")
  keyword ")"
  return (F f t)

parseRule :: Parser Rule
parseRule = do
  l <- parseTerm
  keyword "->"
  r <- parseTerm
  return (l, r)

parseTRS :: Parser TRS
parseTRS = many parseRule

parseAnything :: Parser ()
parseAnything =
  do { _ <- identifier; return () } <|>
  do { keyword "("; _ <- many parseAnything; keyword ")" }

parseCOMMENT :: Spec -> Parser Spec
parseCOMMENT spec = do
  keyword "("
  _ <- many parseAnything
  keyword ")"
  return spec

parseVAR :: Spec -> Parser Spec
parseVAR spec = do
  keyword "("
  keyword "VAR"
  xs <- many identifier
  keyword ")"
  return (spec { _VAR = xs })

parseRULES :: Spec -> Parser Spec
parseRULES spec = do
  keyword "("
  keyword "RULES"
  ctrs <- many parseRule
  keyword ")"
  return (spec { _RULES = _RULES spec ++ convertTRS (_VAR spec) ctrs })

parseSection :: Spec -> Parser Spec
parseSection spec = 
  try (parseVAR spec)
  <|> try (parseRULES spec)
  <|> parseCOMMENT spec

parseEOF :: Spec -> Parser Spec
parseEOF spec = do
  eof
  return spec

parseSections :: Spec -> Parser Spec
parseSections spec = 
  try (parseEOF spec) <|>
  (do { spec' <- parseSection spec; parseSections spec' })

emptySpec :: Spec
emptySpec = Spec {
  _VAR = [],
  _RULES = []
}

parseSpec :: Parser TRS
parseSpec = do
  spec <- parseSections emptySpec
  return (_RULES spec)

-- Reader functions.

readWith :: Parser a -> String -> a
readWith f s =
  case parse f "(input)" s of
    Left e  -> error (show e)
    Right t -> t

readTerm :: String -> Term
readTerm s = readWith parseTerm s

readRule :: String -> Rule
readRule s = readWith parseRule s

readTRS :: String -> TRS
readTRS s = readWith parseTRS s

readSpec :: String -> TRS
readSpec s = readWith parseSpec s

readSpecFile :: String -> IO (Either ParseError TRS)
readSpecFile s = parseFromFile parseSpec s

