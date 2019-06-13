module Utils where

open import Data.List.Base as List using ()
open import Data.Nat using (ℕ; _+_; _≤?_)
import Data.List.Properties as Listₚ
open import Data.String.Base as String
open import Data.String.Unsafe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open ≡-Reasoning

toList-++ : ∀ s t → toList (s ++ t) ≡ toList s List.++ toList t
toList-++ s t = trustMe

length-++ : ∀ s t → String.length (s ++ t) ≡ length s + length t
length-++ s t = begin
  length (s ++ t)                         ≡⟨⟩
  List.length (toList (s ++ t))           ≡⟨ cong List.length (toList-++ s t) ⟩
  List.length (toList s List.++ toList t) ≡⟨ Listₚ.length-++ (toList s) ⟩
  length s + length t                     ∎

length-replicate : ∀ n {c} → length (replicate n c) ≡ n
length-replicate n {c} = begin
  length (replicate n c)           ≡⟨ cong List.length (toList∘fromList (List.replicate n c)) ⟩
  List.length (List.replicate n c) ≡⟨ Listₚ.length-replicate n ⟩
  n                                ∎

module _ {a} {A : Set a} where

  minBy : (A → ℕ) → A → A → A
  minBy f x y with f x ≤? f y
  ... | yes p = x
  ... | no ¬p = y
