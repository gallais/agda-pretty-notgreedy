module Utils where

open import Data.List.Base as List
open import Data.List.NonEmpty
open import Data.List.Properties
open import Data.Maybe
open import Data.Nat.Base
open import Data.Char.Base
open import Data.String.Base as String
open import Data.Vec as Vec
open import Data.BoundedVec as BVec using (BoundedVec)
open import Function
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open ≡-Reasoning

Slength : String → ℕ
Slength = List.length ∘′ String.toList

Sreplicate : ℕ → Char → String
Sreplicate n c = String.fromList (List.replicate n c)

SfromVec : ∀ {n} → Vec Char n → String
SfromVec = String.fromList ∘ Vec.toList

SfromBoundedVec : ∀ {n} → BoundedVec Char n → String
SfromBoundedVec = String.fromList ∘ BVec.toList

toList-++ : ∀ s t → String.toList (s String.++ t) ≡ String.toList s List.++ String.toList t
toList-++ s t = trustMe

Slength-replicate : ∀ n {c} → Slength (Sreplicate n c) ≡ n
Slength-replicate n {c} = begin
  Slength (Sreplicate n c)         ≡⟨ cong List.length (toList∘fromList (List.replicate n c)) ⟩
  List.length (List.replicate n c) ≡⟨ length-replicate n ⟩
  n                                ∎

module _ {a} {A : Set a} where

  minBy : (A → ℕ) → A → A → A
  minBy f x y with f x ≤? f y
  ... | yes p = x
  ... | no ¬p = y

  uncons : List A → Maybe (List⁺ A)
  uncons []       = nothing
  uncons (x ∷ xs) = just (x ∷ xs)
