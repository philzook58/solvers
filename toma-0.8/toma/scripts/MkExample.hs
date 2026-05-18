import System.IO

s :: Int -> String
s n
  | n == 0 = "z"
  | n > 0 = "s(" ++ s (n-1) ++ ")"

divTerm :: Int -> Int -> String
divTerm n m = "div(" ++ s n ++ " ," ++ s m ++ ")"

multTerm :: Int -> Int -> String
multTerm n m = "mult(" ++ s n ++ "," ++ s m ++ ")"

divcnf :: Int -> Int -> Int -> String
divcnf n1 n2 n3 = "cnf(a, negated_conjecture, ( " ++ (divTerm n1 n2) ++ " != " ++ s n3 ++ " ) )."

multcnf :: Int -> Int -> Int -> String
multcnf n1 n2 n3 = "cnf(a, negated_conjecture, ( " ++ (multTerm n1 n2) ++ " != " ++ s n3 ++ " ) )."

-- >>> multcnf 10 10 100
-- "cnf(a, negated_conjecture, ( mult(s(s(s(s(s(s(s(s(s(s(z)))))))))),s(s(s(s(s(s(s(s(s(s(z))))))))))) != s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) ) )."
-- >>> multcnf 5 5 25
-- "cnf(a, negated_conjecture, ( mult(s(s(s(s(s(z))))),s(s(s(s(s(z)))))) != s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))) ) )."
-- >>> multcnf 7 7 49
-- "cnf(a, negated_conjecture, ( mult(s(s(s(s(s(s(s(z))))))),s(s(s(s(s(s(s(z)))))))) != s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z))))))))))))))))))))))))))))))))))))))))))))))))) ) )."
-- >>> multcnf 3 3 9
-- "cnf(a, negated_conjecture, ( mult(s(s(s(z))),s(s(s(z)))) != s(s(s(s(s(s(s(s(s(z))))))))) ) )."
-- >>> multcnf 4 4 16
-- "cnf(a, negated_conjecture, ( mult(s(s(s(s(z)))),s(s(s(s(z))))) != s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(s(z)))))))))))))))) ) )."
-- >>> multcnf 2 2 4
-- "cnf(a, negated_conjecture, ( mult(s(s(z)),s(s(z))) != s(s(s(s(z)))) ) )."
--

mkDivProblem :: Int -> Int -> Int -> IO ()
mkDivProblem n1 n2 n3 = writeFile fname txt
  where
    fname = "examples/div/roundup_division_" ++ show n1 ++ "_" ++ show n2 ++ "_" ++ show n3 ++ ".p"
    txt = "include('roundup_division.ax').\n" ++
          ("% div(" ++ show n1 ++ "," ++ show n2 ++ ") = " ++ show n3 ++ ")\n") ++
          (divcnf n1 n2 n3) ++ "\n"

mkDivBench :: IO ()
mkDivBench = mapM_ (\n -> mkDivProblem (n * n) n n) [2..10]

-- >>> mkDivBench
--
