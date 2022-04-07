module Main where

import Lib
import Data.Foldable
import Data.SBV

main :: IO ()
main = do 
  putStrLn "========= A Reunion In Purple ========="
  people <- puzzle
  putStrLn $ showPeople people
  putStrLn "========= Thanks for coming! ========="

{-


  query $ do
    cs <- checkSat
    case cs of
      Sat -> do
        people <- for people (getPerson)
        pure people
      _ -> error $ "Solver said: " ++ show cs

-}
