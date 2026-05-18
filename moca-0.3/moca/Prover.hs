module Prover where

import Data.List
import Data.Ord
import System.Process
import System.Directory
import System.IO

import Terms
import Rules
import Trie
import TPTP
import Horn
import INF
import ParserForZ3
import ConfluenceCheck
import OrderedRewriting
import EncodingToZ3
import Approximation
import Parameters
import Messages
import Text.ParserCombinators.Parsec

type ProblemType = String

data Result = SAT OTRS [Projection] | UNSAT OTRS [Projection] | Running IntermediateData | GiveUp OTRS deriving Eq
instance Show Result where
  show (SAT otrs proj)   = "# SZS status Satisfiable\n"   ++ showOTRS otrs ++ remarkForCollapsing proj
  show (UNSAT otrs proj) = "# SZS status Unsatisfiable\n" ++ showOTRS otrs ++ remarkForCollapsing proj
  show (Running idata) = "(Running: " ++ (show idata) ++ ")"
  show (GiveUp otrs) = "# SZS status Maybe\n" ++ showOTRS otrs

-- TODO: this IntermediateData should be a record type!
type IntermediateData = (Int, [String], [String], ES, ES, ES, ES, Maybe Precedence)
type IntermediateDB = [(Parameter, Maybe IntermediateData)]

-- second ES and goal are approximated problem (only for SAT)
execution :: IntermediateDB -> [(Int, Parameter)] -> ProblemType ->
  [(String, ((ES, ES, Maybe CertInfo), [HornClause Atom]))] -> Bool -> Either ParseError INFProblem -> IO String
execution idb []                    pt wps _ _ = do { putStrLn ("!Error: invalid parameters\n") ; return undefined }
execution idb ((loop, prm) : lprms) pt wps certFlag infp = do
  if skipCheck prm pt idb then execution idb lprms pt wps certFlag infp
  else do
    let Just ((es, gs, certInfo), hc)
          | certFlag                            = lookup "cert" wps
          | noCondMode prm  && tuplingMode prm  = lookup "nctp" wps
          | noCondMode prm                      = lookup "nc" wps
          |                    tuplingMode prm  = lookup "tp" wps
          | multiSplitIfMode prm                = lookup "msi" wps
          | otherwise                           = lookup "" wps
    let es1 = if cap2Mode prm  then capES 2 es (functionsInES es) else es
    let idata | Just (Just idata0) <- lookup prm idb  = idata0  -- reuse the intermediate data in previous execution of "prm"
              | otherwise                                            -- execute by "prm" for the first time
                  = (freshFunctionSymbolNumber (es1 ++ gs), constants es1, functionsInES gs, es1, es1, gs, [], Nothing)
    result <- phi loop prm idata
    case result of
      SAT otrs proj   -> if pt == "INF" then if certFlag
                                            then return (resultForINF_Infeasible_cert hc es gs otrs proj certInfo infp)
                                            else return (resultForINF_Infeasible hc es gs otrs proj)
                                          else return (resultForTPTP_SAT hc es gs otrs proj)
      UNSAT otrs proj -> if pt == "INF" then return (resultForINF_Maybe otrs proj)
                                          else return (resultForTPTP_UNSAT hc es gs otrs proj)
      Running idata' -> execution (updateIDB prm (Just idata') idb) lprms pt wps certFlag infp
      GiveUp otrs -> execution (updateIDB prm Nothing idb) lprms pt wps certFlag infp
  where updateIDB prm0 mbidata0 idb0 
          = [ (prm1, mbidata1) | (prm1, mbidata1) <- idb0, prm1 /= prm0 ] ++ [(prm0, mbidata0)]

skipCheck prm pt idb  
  | lookup prm idb == Just Nothing     = True -- this parameter has been given up
  | pt == "INF" && inModeForUNSAT prm  = True -- skip UNSAT mode in solving INF problem
  | pt /= "INF" && noCondMode prm      = True -- skip no-condition-mode in solving non-INF-problem
  | noApproximationsByGenalization prm && cap2Mode prm             = True
  | noApproximationsByGenalization prm && divergenceCriticMode prm = True
  | noApproximationsByGenalization prm && noCondMode prm           = True
  | skipMultiSplitIf prm && multiSplitIfMode prm = True
  | otherwise   = False

phi :: Int -> Parameter -> IntermediateData -> IO Result
phi loop prm (ffn, consts, smallprecs, es, c, gs, ces, mprec) = do
    ldump
    result <- phi2 (loop, loop) prm ffn consts smallprecs es c gs ces mprec
    let result' | UNSAT otrs _ <- result, inModeForSAT prm = GiveUp otrs
                | otherwise                                = result
    return result'
  where ldump = if lightDumpInfo prm then putStrLn (show (loop, prm)) else return ()

phi2 :: (Int, Int) -> Parameter -> Int -> [String] -> [String] -> ES -> ES -> ES -> ES -> Maybe Precedence -> IO Result
phi2 (   0, initloop) prm ffn consts smallprecs es c gs ces mprec = return (Running (ffn, consts, smallprecs, es, c, gs, ces, mprec))
phi2 (loop, initloop) prm ffn consts smallprecs es c gs ces mprec = do
    dump1
    let (ffn', c', ces', consts') = preprocessing prm (ffn, c, ces, consts)
    motrsts <- createRC prm smallprecs c' mprec
    case motrsts of 
      Nothing -> return (GiveUp ([],[],[]))
      Just otrsts -> do
        let sc = createSC prm consts' es otrsts
        dump2 otrsts sc
        let maybeResult_U                       = unsat otrsts sc consts' gs
        let maybeResult_S | inModeForUNSAT prm  = Nothing                     -- to avoid sparing time for checking satisfiability
                          | otherwise           = sat prm otrsts sc consts' gs
        case (maybeResult_U, maybeResult_S) of 
          (Just result,           _) -> return result
          (          _, Just result) -> return result
          (          _,           _) -> do
            (c'', mprec') <- postprocessing prm mprec otrsts sc c' 
            phi2 (loop - 1, initloop) prm ffn' consts' smallprecs es c'' gs ces' mprec'
    where dump1 = if dumpInfo prm 
                  then putStrLn ("--- " ++ show prm ++ " ---\nloop " ++ show (initloop - loop + 1) 
                                  ++ " / " ++ show initloop ++ " ...") 
                  else if lightDumpInfo prm
                    then putStrLn ("loop " ++ show (initloop - loop + 1) ++ " ...") 
                    else return ()
          dump2 otrsts sc = if dumpInfo prm then putStrLn (showRC otrsts ++ showSC sc) else return ()

preprocessing :: Parameter -> (Int, ES, ES, [String]) -> (Int, ES, ES, [String])
preprocessing prm (ffn, c, ces, consts) = if tietzeConversionMode prm 
                                             then tietzeConversion ffn c ces consts
                                             else (ffn, c, ces, consts) 

postprocessing :: Parameter -> Maybe Precedence -> [OTRST] -> [(ES, OTRST)] -> ES -> IO (ES, Maybe Precedence)
postprocessing prm mprec otrsts sc c' = do
    let newrules = [ e | (es0, _) <- sc, e <- es0 ]
    let c'' = sortES (nubBy isSameEquation (c' ++ newrules))
    dump3 c' newrules
    let mprec' = if fixedOrderMode prm then Just prec0 else mprec  where ((_, _, prec0), _) : _ = otrsts
    return (c'', mprec')
  where dump3 c newrules = if dumpInfo prm then putStrLn (showC c newrules) else return ()


unsat :: [OTRST] -> [(ES, OTRST)] -> [String] -> ES -> Maybe Result
unsat otrsts sc consts gs 
  | Just result <- unsat1 otrsts consts gs  = Just result
  | Just result <- unsat2 sc gs             = Just result
  | otherwise                               = Nothing

unsat1 :: [OTRST] -> [String] -> ES -> Maybe Result
unsat1 otrsts consts gs
  | (otrs0, _) : _ <- [ otrst | otrst <- otrsts, someGoalJoins otrst ] = Just (UNSAT otrs0 []) 
  | otherwise                                                          = Nothing
  where someGoalJoins otrst = or [ OrderedRewriting.join otrst consts l r | (l, r) <- gs] 

unsat2 :: [(ES, OTRST)] -> ES -> Maybe Result
unsat2 sc gs 
  | otrs0 : _ <- someGoalIsGenerated  = Just (UNSAT otrs0 [])
  | otherwise                         = Nothing
  where someGoalIsGenerated = [ mergeOTRSAndES (otrs, es0) | (es0, (otrs, _)) <- sc, existCommonES gs es0 ]
        mergeOTRSAndES ((es1, trs1, prec1), es2) = orient (es1 ++ trs1 ++ es2) prec1


sat :: Parameter -> [OTRST] -> [(ES, OTRST)] -> [String] -> ES -> Maybe Result
sat prm otrsts sc consts gs 
  | Just result <- sat1 sc                    = Just result
  | Just result <- sat2 prm otrsts consts gs  = Just result
  | otherwise                                 = Nothing

sat1 :: [(ES, OTRST)] -> Maybe Result
sat1 sc 
  | otrs0 : _ <- [ otrs | (es0, (otrs, _)) <- sc, es0 == [] ]  = Just (SAT otrs0 [])
  | otherwise                                                  = Nothing

sat2 :: Parameter -> [OTRST] -> [String] -> ES -> Maybe Result
sat2 prm otrsts consts gs 
  | (otrs0, proj0) : _ <- [ (otrs, proj) 
                            | otrst <- otrsts, 
                              (otrs, proj) <- approximations prm otrst,
                              let otrst' =  createTrie otrs,
                              unsat1 [otrst'] consts gs == Nothing,
                              nonGroundJoinableECPs otrst' consts == [] ]
    = Just (SAT otrs0 proj0)
  | otherwise
    = Nothing


--- RC
createRC :: Parameter -> [String] -> ES -> Maybe Precedence -> IO (Maybe [OTRST])
createRC prm smallprecs c mprec
  | Just prec <- mprec  = return (Just [createTrie (orient c (nub (prec ++ functionsInES c)))]) -- fixed order
  | c == [] = return (Just [createTrie ([], [], [])])
  | otherwise = do
      motrss <- searchMaximalTRS prm smallprecs (maxOfNumOfTRSs prm) (taggedES "a" c ++ taggedES "b" (inverse c)) []
      case motrss of 
        Just otrss -> return (Just [ createTrie (sortES (lrReduction trs es), sortES (interReduction trs), prec) 
                                   | (es, trs, prec) <- otrss ])
        Nothing -> return Nothing
    where taggedES str es = [ (str ++ show i, e) | (i, e) <- zip [0..] es ]

searchMaximalTRS :: Parameter -> [String] -> Int -> [(String, Equation)] -> [(Precedence, [String])] -> IO (Maybe [OTRS])
searchMaximalTRS prm smallprecs k tages ptagss
  | k == 0     = return (Just (ptagssToOTRS ptagss))
  | otherwise  = do
    mbtags <- searchMaximalTags prm smallprecs tages [ tags | (_, tags) <- ptagss ]
    case mbtags of
      Just ptags  -> searchMaximalTRS prm smallprecs (k - 1) tages (ptags : ptagss)
      Nothing     -> 
        case ptagss of 
          []        -> return Nothing
          otherwise -> return (Just (ptagssToOTRS ptagss))
  where ptagssToOTRS ptagss0 = emptyIfNull [ (tags2ES tags, tags2TRS tags, prec)
                                           | (prec, tags) <- ptagss0 ]
        tags2ES tags0 = [ e | (c : cs, e) <- tages, c == 'a', cs `notElem` [ ds | _ : ds <- tags0 ] ]
        tags2TRS tags0 = [ r | tag <- tags0, Just r <- [lookup tag tages] ]
        emptyIfNull []      = [([], [], [])]
        emptyIfNull otrss  = otrss

searchMaximalTags :: Parameter -> [String] -> [(String, Equation)] -> [[String]] -> IO (Maybe (Precedence, [String]))
searchMaximalTags prm smallprecs tages old_tagss = do
  let functionDict = [ (oldf, "f" ++ show i) 
                     | (i, oldf) <- zip [0..] (functionsInES [ e | (_, e) <- tages ]) ]
  let tages' = [ (tag, (replaceFunctionSymbol functionDict s, replaceFunctionSymbol functionDict t))  
               | (tag, (s, t)) <- tages ]
  let smallprecs' = [ rename functionDict s | s <- smallprecs ]
  mbptags <- callZ3 prm smallprecs' tages' old_tagss
  case mbptags of
    Just (prec, tags)   -> return (Just ([ originalString functionDict f | f <- prec ], tags))
    Nothing             -> return Nothing

callZ3 :: Parameter -> [String] -> [(String, Equation)] -> [[String]] -> IO (Maybe (Precedence, [String]))
callZ3 prm smallprecs tages old_tagss = do
    (iname, oname) <- getOrCreateTempfile prm
    let istr = inputForZ3 smallprecs tages old_tagss
    writeFile iname istr
    system ("z3 " ++ iname ++ " > " ++ oname)
    -- system ("echo \"" ++ istr ++ "\"" ++ " | z3 -in > " ++ oname)
    if leaveInputFile prm then return () else removeFile iname
    ostr <- readFile oname
    if leaveOutputFile prm then return () else removeFile oname
    z3result <- readZ3Output ostr
    let mbptags | Just rs <- z3result  
                  = Just ( [ f | (f, _) <- sortBy (comparing (Down . snd)) (fis rs) ], 
                           [ tag | (tag, b) <- tagbs rs, b ] )
                | otherwise = Nothing
    return mbptags
  where dbgi istr0 = do (iname, hi) <- openTempFile "." z3InputFile
                        hClose hi
                        writeFile iname istr0
        fis   rs0 = [ (s, n) | (s, I n) <- rs0 ]
        tagbs rs0 = [ (s, b) | (s, ParserForZ3.B b) <- rs0 ]
  
getOrCreateTempfile :: Parameter -> IO (String, String)
getOrCreateTempfile prm = 
  case (tempfileNameI prm, tempfileNameO prm) of 
    (Just fi, Just fo) -> return (fi, fo)
    (_, _) -> do
      (iname, hi) <- openTempFile "." z3InputFile 
      hClose hi
      (oname, ho) <- openTempFile "." z3OutputFile 
      hClose ho
      removeFile oname  -- for the case process terminates in executing z3
      return (iname, oname)

z3InputFile = "__inputfile.txt"
z3OutputFile = "__outputfile.txt"



createSC :: Parameter -> [String] -> ES -> [OTRST] -> [(ES, OTRST)]
createSC prm consts es otrsts 
  = [ (filter1 n (filter2 d (newrules otrst)) ++ newrules_dc otrst, otrst) | otrst <- otrsts ]
  where 
    (n, d) = (numOfRemainingEquations prm, maxEquationSize prm)
    filter1 n0 es0  = if n0 > 0                 then take n0 es0 else es0
    filter2 d0 es0  = if d0 > 0 && es_ltd /= [] then es_ltd      else es0
      where es_ltd = [ e | e <- es0, sizeOfEquation e < d0 ]
    newrules otrst0@((es', trs', _), _)
      = [ e | e <- nonGroundJoinableECPs otrst0 consts, 
              not (equationInES e (es' ++ trs')) ]
    newrules_dc otrst0@((es', trs', _), _) 
      = if divergenceCriticMode prm 
          then [ e | e <- (divergenceCritic (es' ++ trs')) , 
                     not (equationInES e (es' ++ trs')) ]
          else []

tietzeConversion :: Int -> ES -> ES -> [String] -> (Int, ES, ES, [String])
tietzeConversion ffn c ces consts = (ffn', c', ces', consts')
  where   
    ces0 = [ e0 | e0 <- constEquations c, not (equationInES e0 ces)]
    ffn' = ffn + (length ces0)
    c' = [ e | e <- c, not (equationInES e ces0)] 
         ++ [ (s, F (freshFunctionName (i + ffn)) []) | (i, (s, _)) <- zip [0..] ces0 ]
    ces' = ces ++ ces0
    consts' = consts ++ [ freshFunctionName (i + ffn) | (i, (s, _)) <- zip [0..] ces0 ]







showInputES :: ES -> String
showInputES es = "Input:\n" 
                 ++ showES es 
                 ++ "\n\n"
showRC :: [OTRST] -> String
showRC rc = "-- R(C) --\n" 
            ++ intercalate "\n" [ "< R" ++ show i ++ " >\n" 
                                  ++ showOTRS otrs 
                                | (i, (otrs, _)) <- zip [0..] rc ] 
            ++ "\n\n"
showSC :: [(ES, OTRST)] -> String
showSC sc = "-- S(C) --\n" 
            ++ intercalate "\n" [ "< S" ++ show i ++ " >\n" 
                                  ++ showPrecedence p ++ "\n" 
                                  ++ showES cp 
                                | (i, (cp, ((_, _, p), _))) <- zip [0..] sc ] 
            ++ "\n\n"
showC :: ES -> ES -> String
showC c nes = "-- C --\n" 
              ++ showES c 
              ++ "\n\t----------------------------\n" 
              ++ showES [ e | e <- nubBy isSameEquation nes, not (equationInES e c) ]
              ++ "\n\n"

