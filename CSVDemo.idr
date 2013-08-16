module Main

import CSV
import FileEval

main : IO ()
main = do
  str <- readFile "/dev/stdin"
  case parseString csv str of
    [] => putStrLn "what"
    (x::xs) => putStrLn (showBlock (last (x::xs) refl))