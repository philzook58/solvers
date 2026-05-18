module ParserForZ3 where

import Terms
import Substitutions
import Rules
import Text.ParserCombinators.Parsec

-- [DATA] Term
data IntOrBool = I Int | B Bool deriving Eq
instance Show IntOrBool where
  show (I n) = show n
  show (B b) = show b


number :: Parser Int
number = do ds <- many1 digit
            return (read ds)

keyword :: String -> Parser ()
keyword s = do { string s; spaces; return () }

symbol :: Parser String
symbol = do { x <- many1 (alphaNum); spaces; return x }

positive :: Parser Int
positive = do { x <- number;
                return x }
negative :: Parser Int
negative = do { keyword "(- ";  x <- number; keyword ")";
                return (-x) }
integer :: Parser Int
integer = try positive <|> negative

true :: Parser Bool
true = do { keyword "true"; 
            return True }
false :: Parser Bool
false = do { keyword "false"; 
             return False }
bool :: Parser Bool
bool = try true <|> false

intResult :: Parser (String, IntOrBool)
intResult = do { keyword "("; f <- symbol; spaces; n <- integer; keyword ")";
                 return (f, I n) }

boolResult :: Parser (String, IntOrBool)
boolResult = do { keyword "("; f <- symbol; spaces; b <- bool; keyword ")";
                  return (f, B b) }

result :: Parser (String, IntOrBool)
result = try intResult <|> boolResult

results_sat :: Parser (Maybe [(String, IntOrBool)])
results_sat = do { keyword "sat"; spaces;  keyword "("; ibs <- many result;  keyword ")"; 
                   return (Just ibs) }

results_unsat :: Parser (Maybe [(String, IntOrBool)])
results_unsat = do { keyword "unsat"; spaces; many anyChar; 
                     return Nothing }

results :: Parser (Maybe [(String, IntOrBool)])
results = try results_sat <|> results_unsat

-- Reader
readZ3Output :: String -> IO (Maybe [(String, IntOrBool)])
readZ3Output s = do
  case parse results "" s of
    Left err -> error ("Moca failed to read the output of Z3:\n" ++ show err)
    Right res -> return res

