module Main where

import System.Environment       (getArgs)
import System.FilePath          (dropExtension, replaceExtension)
import System.Process           (callProcess)

main :: IO ()
main = runJava

runJava :: IO ()
runJava = do
  args <- getArgs
  let filePath  = args !! 0
  callProcess "javac" [filePath]
  callProcess "java"  [dropExtension filePath]
  callProcess "rm"    [replaceExtension filePath "class"]
