module Lib (
    someFunc
) where

import Show
import Read

someFunc :: IO ()
someFunc = do
    putStrLn $ "Hello! This is my course work"