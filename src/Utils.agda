module Utils where

open import Data.List.Base as List
open import Data.List.NonEmpty
open import Data.Maybe
open import Data.Nat.Base
open import Data.String.Base as String
open import Function
open import Relation.Nullary

Slength : String → ℕ
Slength = List.length ∘′ String.toList

module _ {a} {A : Set a} where

  minBy : (A → ℕ) → A → A → A
  minBy f x y with f x ≤? f y
  ... | yes p = x
  ... | no ¬p = y

  uncons : List A → Maybe (List⁺ A)
  uncons []       = nothing
  uncons (x ∷ xs) = just (x ∷ xs)
