module Main where

import Control.Monad
import Data.Foldable
import Data.SBV
import Lib

main :: IO ()
main = do
  putStrLn "========= A Reunion In Purple ========="
  (people, murders) <- reunion
  putStrLn $ showPeople people
  for_ murders $ \(victim, killers) -> 
    when (killers /= []) $ do
      putStrLn $ "Victim: " ++ show victim
      putStrLn $ "Possible Killers: " ++ show killers
  putStrLn "========= Thanks for coming! ========="
