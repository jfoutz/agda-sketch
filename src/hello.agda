module Hello where

open import Agda.Builtin.IO using (IO)
open import Data.String using (String)
open import Data.Unit using (⊤)

postulate putStrLn : String -> IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = putStrLn . T.unpack #-}

main : IO ⊤
main = putStrLn "Hello world!"
