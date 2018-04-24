module Main where

open import Data.SExpr
open import Function
open import Text.Pretty.Interface
open import Text.Pretty.NonEmpty
open import IO

main = run (putStr (render (layouts.D ∋ pretty Test.testData)))
