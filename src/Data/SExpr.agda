module Data.SExpr where

open import Size
open import Data.Unit
open import Data.List.Base
open import Data.String.Base
open import Function

data SExpr (i : Size) : Set where
  Node : {j : Size< i} → List (SExpr j) → SExpr i
  Atom : String → SExpr i

open import Text.Pretty.Interface

pretty : ∀ {ℓ} {d : Set ℓ} {{_ : Doc d}} → ∀ {i} → SExpr i → d
pretty (Atom st) = text st
pretty (Node xs) = text "("
                <> (sep $ map pretty xs)
                <> text ")"

module Test where

  abcd : SExpr ∞
  abcd = Node $ map Atom $ "a" ∷ "b" ∷ "c" ∷ "d" ∷ []

  abcd₄ : SExpr ∞
  abcd₄ = Node $ replicate 4 abcd

  testData : SExpr ∞
  testData = Node
           $ Node (Atom "abcde" ∷ abcd₄ ∷ [])
           ∷ Node (Atom "abcdefgh" ∷ abcd₄ ∷ [])
           ∷ []
