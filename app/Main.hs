module Main where

import Data.Foldable
import Data.SBV
import Lib

main :: IO ()
main = do
  putStrLn "========= A Reunion In Purple ========="
  people <- reunion
  putStrLn $ showPeople people
  putStrLn "========= Thanks for coming! ========="
