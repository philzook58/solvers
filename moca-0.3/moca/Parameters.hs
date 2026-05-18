module Parameters where

import Data.List

type Parameter = (Int, Int, Int, [String])

-- (numOfLoop, maxNumOfTRSs, numOfRemainingEquations, maxEquationSize, modes)
defaultParameters :: [(Int, Parameter)]
defaultParameters = [
                       (2, (1, 7, -1, ["-fo"])), -- for unsat
                       (2, (1, 7, 20, ["-tc", "-msi"])), -- for sat
                       (2, (1, 7, 20, ["-tc", "-nc", "-tp"])), -- for INF
                       (2, (1, 7, 20, ["-tc", "-nc"])), -- for INF
                       (2, (1, 7, 20, ["-tc"])),
                       (3, (3, 1, 20, ["-tc", "-msi"])), -- for sat
                       (3, (3, 1, 20, ["-tc", "-nc", "-tp"])), -- for INF
                       (3, (3, 1, 20, ["-tc", "-nc"])), -- for INF
                       (3, (3, 1, 20, ["-tc"])),
                       (1, (1, 100, -1, ["-fo"])), -- for unsat
                       (2, (1, 7, -1, ["-fo"])), -- for unsat
                       (2, (1, 7, 20, ["-tc", "-msi"])),  -- for sat
                       (2, (1, 7, 20, ["-tc", "-nc", "-tp"])),  -- for INF
                       (2, (1, 7, 20, ["-tc", "-nc"])), -- for INF
                       (2, (1, 7, 20, ["-tc"])),
                       (3, (3, 1, 20, ["-tc", "-msi"])), -- for sat
                       (3, (3, 1, 20, ["-tc", "-nc", "-tp"])), -- for INF
                       (3, (3, 1, 20, ["-tc", "-nc"])), -- for INF
                       (3, (3, 1, 20, ["-tc"])),
                       (1, (1, 100, -1, ["-fo"])), -- for unsat
                       (2, (1, 14, 20, ["-cap2", "-msi"])), -- for sat
                       (2, (1, 14, 20, ["-cap2", "-nc", "-tp"])), -- for INF
                       (2, (1, 14, 20, ["-cap2", "-nc"])), -- for INF
                       (2, (1, 14, 20, ["-cap2"])), -- for sat
                       (2, (1, 7, 20, ["-tc", "-dc"])), -- for sat
                       (5, (1, 2, 20, ["-tc"])),
                       (5, (1, 7, 20, ["-tc", "-msi"])), -- for sat
                       (5, (1, 7, 20, ["-tc", "-nc", "-tp"])), -- for INF
                       (5, (1, 7, 20, ["-tc", "-nc"])), -- for INF
                       (5, (1, 7, 20, ["-tc"])),
                       (12, (1, 7, -1, ["-fo"])), -- for unsat
                       (1, (1, 100, -1, ["-fo"])), -- for unsat
                       (2, (1, 14, 20, ["-cap2", "-msi"])), -- for sat
                       (2, (1, 14, 20, ["-cap2", "-nc", "-tp"])), -- for INF
                       (2, (1, 14, 20, ["-cap2", "-nc"])), -- for INF
                       (2, (1, 14, 20, ["-cap2"])), -- for sat
                       (2, (1, 7, 20, ["-tc", "-dc"])), -- for sat
                       (5, (3, 1, 20, ["-tc", "-msi"])), -- for sat
                       (5, (3, 1, 20, ["-tc", "-nc", "-tp"])), -- for INF
                       (5, (3, 1, 20, ["-tc", "-nc"])), -- for INF
                       (5, (3, 1, 20, ["-tc"])),
                       (12, (1, 7, -1, ["-fo"])), -- for unsat
                       (1, (1, 100, -1, ["-fo"])), -- for unsat
                       (1, (1, 14, 20, ["-cap2", "-msi"])), -- for sat
                       (1, (1, 14, 20, ["-cap2", "-nc", "-tp"])), -- for INF
                       (1, (1, 14, 20, ["-cap2", "-nc"])), -- for INF
                       (1, (1, 14, 20, ["-cap2"])), -- for sat
                       (1, (1, 7, 20, ["-tc", "-dc"])), -- for sat
                       (12, (1, 7, -1, ["-fo"])), -- for unsat
                       (1, (1, 100, -1, ["-fo"])), -- for unsat
                       (1, (1, 14, 20, ["-cap2", "-msi"])), -- for sat
                       (1, (1, 14, 20, ["-cap2", "-nc", "-tp"])), -- for INF
                       (1, (1, 14, 20, ["-cap2", "-nc"])), -- for INF
                       (1, (1, 14, 20, ["-cap2"])), -- for sat
                       (5, (3, 1, 20, ["-tc", "-msi"])), -- for sat
                       (5, (3, 1, 20, ["-tc", "-nc", "-tp"])), -- for INF
                       (5, (3, 1, 20, ["-tc", "-nc"])), -- for INF
                       (5, (3, 1, 20, ["-tc"])),
                       (12, (1, 7, -1, ["-fo"])), -- for unsat
                       (1, (1, 100, -1, ["-fo"])) -- for unsat
                     ]

-- defaultParameters = [
--                        (5, (1, 7, -1, ["-fo", "-tc"])), -- for unsat
--                        (5, (1, 14, 20, ["-cap2"])), -- for sat
--                        (10, (1, 7, 20, ["-tc"])),
--                        (10, (3, 1, 20, ["-tc"])),
--                        (90, (1, 7, -1, ["-fo", "-tc"])), -- for unsat
--                        --  (12, (1, 7, 20, ["-dc"])), 
--                        (-1, (1, 7, 20, ["-tc"])) 
--                      ]



-- parameter
maxOfNumOfTRSs :: Parameter -> Int
maxOfNumOfTRSs (k, _, _, _) = k
numOfRemainingEquations :: Parameter -> Int
numOfRemainingEquations (_, n, _, _) = n
maxEquationSize :: Parameter -> Int
maxEquationSize (_, _, d, _) = d
modes :: Parameter -> [String]
modes (_, _, _, strs) = strs
tietzeConversionMode :: Parameter -> Bool
tietzeConversionMode prm = "-tc" `elem` (modes prm)
cap2Mode :: Parameter -> Bool
cap2Mode prm = "-cap2" `elem` (modes prm)
divergenceCriticMode :: Parameter -> Bool
divergenceCriticMode prm = "-dc" `elem` (modes prm)
fixedOrderMode :: Parameter -> Bool
fixedOrderMode prm = "-fo" `elem` (modes prm)
noCondMode :: Parameter -> Bool
noCondMode prm = "-nc" `elem` (modes prm)
tuplingMode :: Parameter -> Bool
tuplingMode prm = "-tp" `elem` (modes prm)
multiSplitIfMode :: Parameter -> Bool
multiSplitIfMode prm = "-msi" `elem` (modes prm)
leaveInputFile :: Parameter -> Bool
leaveInputFile prm = "-dbgi" `elem` (modes prm)
leaveOutputFile :: Parameter -> Bool
leaveOutputFile prm = "-dbgo" `elem` (modes prm)
dumpInfo :: Parameter -> Bool
dumpInfo prm = "-dbg" `elem` (modes prm)
lightDumpInfo :: Parameter -> Bool
lightDumpInfo prm = "-ldbg" `elem` (modes prm)
tempfileNameI :: Parameter -> Maybe String
tempfileNameI prm | md0 : _ <- [ md | md <- modes prm, "-tmpi=" `isPrefixOf` md ]
                    = Just (drop (length "-tmpi=") md0)
                  | otherwise                                                     
                    = Nothing
tempfileNameO :: Parameter -> Maybe String
tempfileNameO prm | md0 : _ <- [ md | md <- modes prm, "-tmpo=" `isPrefixOf` md ]
                    = Just (drop (length "-tmpo=") md0)
                  | otherwise                                                     
                    = Nothing

splitIfwithAllVariablesMode :: [(Int, Parameter)] -> Bool
splitIfwithAllVariablesMode lprms = or [ "--siav" `elem` (modes prm) | (_, prm) <- lprms ]
skipMultiSplitIf ::  Parameter -> Bool
skipMultiSplitIf prm = "--smsi" `elem` (modes prm)

noApproximationsByGenalization :: Parameter -> Bool
noApproximationsByGenalization prm = "-nag" `elem` (modes prm)
noApproximationsByProjection :: Parameter -> Bool
noApproximationsByProjection prm = "-nap" `elem` (modes prm)

addMode :: String -> Parameter -> Parameter
addMode md prm = addModes [md] prm
addModes :: [String] -> Parameter -> Parameter
addModes mds (k, n, d, strs) = (k, n, d, nub (strs ++ mds))

addModesToEachParameter :: [String] -> [Parameter] -> [Parameter]
addModesToEachParameter mds prms = [ addModes mds prm | prm <- prms ] 


inModeForSAT :: Parameter -> Bool
inModeForSAT prm = cap2Mode prm || divergenceCriticMode prm || noCondMode prm || multiSplitIfMode prm
inModeForUNSAT :: Parameter -> Bool
inModeForUNSAT prm = fixedOrderMode prm



unknownMode :: [(Int, Parameter)] -> Maybe String
unknownMode [] = Nothing
unknownMode ((_, (_, _, _, mds)) : lprms) 
  | umd : _ <- unknownModes mds = Just umd
  | otherwise                   = unknownMode lprms
  where unknownModes mds0 = [ md | md <- mds0, 
                                  (  md `notElem` knownModes 
                                   && and [ not (pre `isPrefixOf` md) | pre <- knownPrefixes ] ) ]

knownModes = ["-tc", "-cap2", "-dc", "-gx", "-fo", "-nc", "-tp", 
              "-msi", "-dbgi", "-dbgo", "-dbg", "-ldbg", "-help", 
              "--help", "-nap", "-nag", "--siav", "--smsi", "--cert", "-cert"]
knownPrefixes = ["-tmpi=", "-tmpo="]

helpMode :: [(Int, Parameter)] -> Bool
helpMode [] = False
helpMode ((_, (_, _, _, mds)) : _) = "-help" `elem` mds || "--help" `elem` mds

-- certification by CeTA
certMode :: [(Int, Parameter)] -> Bool
certMode [] = False
certMode ((_, (_, _, _, mds)) : _) = "-cert" `elem` mds || "--cert" `elem` mds
