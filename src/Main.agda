module Main where

open import Data.String.Base
open import Data.List.Base
open import Data.SExpr
open import Function
open import Text.Pretty.Interface
open import Text.Pretty.Refined
open import Coinduction
open import IO

display : SExpr _ → ∞ (IO _)
display s = ♯ (putStr $ render (layouts.Bs ∋ pretty s))

main = run
     $ display Test.abcd
     >> ♯ (display Test.abcd₄
     >> display Test.testData)
