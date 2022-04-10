module Main where

import Control.Monad
import Data.Foldable
import Data.SBV
import Lib

main :: IO ()
main = do
  putStrLn "========= A Reunion In Purple ========="
  (people, murders1, murder2, murders3, observables) <- reunion
  putStrLn $ showPeople people murders1 murder2 murders3
  putStrLn "========= Thanks for coming! ========="
  putStrLn observables
