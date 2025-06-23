{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Environment
import System.IO
import System.Timeout
import System.TimeIt

import Data.List
import Data.TPTP.Pretty
import Data.Text
import Data.TPTP.Parse.Text
import Data.TPTP
import Data.Attoparsec.Text
import Data.Set
import qualified Data.Set as Set


import           Control.Applicative
import           Database.SQLite.Simple
import           Database.SQLite.Simple.FromRow
import Control.Monad

import Context
import Prover


import Control.Concurrent (forkIO, killThread, threadDelay)
import Control.Concurrent.MVar (newMVar, swapMVar, takeMVar)
import Control.Exception (evaluate)
import Data.List (foldl')


{-|
  The 'unpackformulaunits' looks for FOF formulas in the list of TPTP units.
  It returns the list of FOF formulas form the first argument, of type 'TPTP'.
-}
unpackformulaunits :: TPTP -> (Context, Set (FirstOrder Unsorted))
unpackformulaunits (TPTP h) =
  let (assms, gls) = unpackformulaunits_h h (Set.empty,Set.empty) in
      (from_assumptions assms, gls)


unpackformulaunits_h :: [Unit] -> (Set Assumption_t, Set (FirstOrder Unsorted)) -> (Set Assumption_t, Set (FirstOrder Unsorted))
unpackformulaunits_h [] acc = acc
unpackformulaunits_h (h:tl) (lfst,lsnd) =
  case h of
    Include _ _ -> unpackformulaunits_h tl (lfst,lsnd)
    Unit _ decl _ ->
      let frm = form_from_decl decl
          rl = goal_role decl
      in case rl of
          Nothing -> unpackformulaunits_h tl (lfst, lsnd)
          Just is_goal -> if is_goal
            then unpackformulaunits_h tl (lfst, Set.union frm lsnd)
            else
            let nfrm = Set.map (\ frml -> (Aspn frml Fresh)) frm
            in unpackformulaunits_h tl (Set.union nfrm lfst, lsnd)


{-|
  The 'form_from_decl' extract FOF formulas from a TPTP Declaration.
  It returns the singleton set with the FOF formula to make further processing easy.
-}
form_from_decl :: Declaration -> Set (FirstOrder Unsorted)
form_from_decl decl =
  case decl of
    Sort _ _ -> Set.empty
    Typing _ _ -> Set.empty
    Formula _ fof ->
      case fof of
        CNF _ -> Set.empty
        FOF form -> Set.singleton form
        TFF0 form -> Set.empty
        TFF1 form -> Set.empty

goal_role decl =
  case decl of
    Sort _ _ -> Nothing
    Typing _ _ -> Nothing
    Formula role fof ->   
      case role of
        Standard Axiom -> Just False
        Standard Hypothesis -> Just True
        Standard Definition -> Just False
        Standard Assumption -> Just False
        Standard Lemma -> Just False
        Standard Theorem -> Just False
        Standard Corollary -> Just False
        Standard Conjecture -> Just True
        Standard NegatedConjecture -> Nothing
        Standard Plain -> Nothing
        Standard FiDomain -> Nothing
        Standard FiFunctors -> Nothing
        Standard FiPredicates -> Nothing
        Standard Unknown -> Nothing
        Extended _ -> Nothing

{-|
  The 'presentproving' accummulates progress information concerning the proving process.
  It tries to prove the formula in the second argument, of type 'FirstOrder Unsorted'. 
-}
presentproving :: Context -> [Maybe Measure_t] -> FirstOrder Unsorted -> [Maybe Measure_t]
presentproving ctx lst fof =
  (prover ctx fof (MInt 100)) : lst -- TODO: this should rather be some formula depth

{-|
  The 'proveformulaunits' tries to prove a parsed TPTP file.
  It tries to prove the formula in the first argument, of type 'Result TPTP'. 
-}
proveformulaunits :: Result TPTP -> [Maybe Measure_t]
proveformulaunits parsed  =
  case parsed of
    Done i res ->
      let (assmpt,goals) = (unpackformulaunits res)
      in Data.List.foldl (presentproving assmpt) [] goals
    Fail i i' i'' -> [Just (MError "Failed parsing 1")]
    Partial ppars ->
      do
        dparsing <- return (ppars (pack ""))
        case dparsing of
           Done i res -> let (assumpt, goals) = unpackformulaunits res
                         in Data.List.foldl (presentproving assumpt) [] goals
           Fail i i' i'' -> [Just (MError ("Failed parsing 2 before" ++ (unpack i) ++ "Ctxt" ++ (show i')))]
           Partial pparsing -> [Just (MError "Failed partial parsing")]


printUsage :: String -> IO ()
printUsage progName = do
    putStrLn ("Usage:" ++ progName ++ " -f <filename>")
    putStrLn ("or:")
    putStrLn (progName ++ " -d <from> <to> <database filename>")


data FrmRes = FrmRes  { formula :: String, id :: Int } deriving (Show)


instance FromRow FrmRes where
    fromRow = FrmRes <$> field <*> field

loop :: Integer -> Integer -> (Integer -> IO()) -> IO()
loop m n f = if m == n then return ()
             else
                do
                  (f m)
                  loop (m+1) n f

caselist :: [Maybe Measure_t] -> IO()
caselist [] = return ()
caselist (hd:tl) = case hd of
                     Nothing -> caselist tl
                     Just (MError s) -> caselist tl
                     Just (MInt n) -> caselist tl


proveList :: Connection -> Integer -> FrmRes -> IO()
proveList conn no r = do
  parsed <- return (parseTPTP (pack (formula r)))
  mvar <- newMVar [Just (MError "Timeout")]
  mtime <- newMVar 5.9
  let compute = do
                  (tt, x) <- timeItT $ (do
                                          y <- return $! (proveformulaunits parsed)
                                          caselist y
                                          return y)
                  _ <- swapMVar mvar x
                  _ <- swapMVar mtime tt
                  hFlush stdout
                  return ()
  putStrLn "Thread started"
  tid <- forkIO (compute)
  putStrLn "Enter delay"
  threadDelay $ 100000
  putStrLn "Delay ends"
  killThread tid
  putStrLn "Thread killed"
{-  result <- timeout (1 *1000000) $! compute -}
{-  result <- return $! compute -}
{-  _ <- compute -}
  result <- takeMVar mvar
  rtime <- takeMVar mtime
  putStrLn "Result retrieved"
  putStrLn (show rtime)
  hFlush stdout
  putStrLn (show result)
  hFlush stdout
  putStrLn "Result printed"
  hFlush stdout
  executeNamed conn "UPDATE formulas SET statusq1 = :str, rtimevq1 = :rt WHERE id = :id" [":str" := (show result), ":rt" := rtime, ":id" := no]
  {- print (formula r) -}

main :: IO ()
main = do  
   args <- getArgs
   progName <- getProgName
   (case args of
         []          ->  printUsage progName
         (hd1:tl) ->
             if hd1 == "-f" then
                (case tl of
                 []       -> putStrLn "Give file name after -f"
                 (hd1:tl) ->
                       do
                         tpstring <- readFile hd1
                         parsed <- return (parseTPTP (pack tpstring))
                         result <- return (proveformulaunits parsed)
                         putStrLn (show result))
             else
               if hd1 == "-d" then
                 (case tl of
                     (frm:to:dbname:tl)       -> 
                         do
                           conn <- open dbname
                           let i = (read frm) :: Integer
                           let ito = (read to) :: Integer
                           let action x = do
                                 putStrLn ("ooooooooooooooooooooooooooooooooooooooooooooooooooooooo")
                                 putStrLn (show x)
                                 r <- queryNamed conn "SELECT formula, id from formulas where id = :id"  [":id" := x] :: IO [FrmRes];
                                 mapM_ (proveList conn x) r
                           loop i ito action
                           close conn
                     _ -> do
                           putStrLn ("Use as follows: " ++ progName ++ " -d <from> <to> <database filename>"))
               else
                 printUsage progName

     )
