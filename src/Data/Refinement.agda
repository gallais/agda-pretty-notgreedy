module Data.Refinement where

open import Level
open import Function

record Refine {a p} (A : Set a) (P : A → Set p) : Set (a ⊔ p) where
  constructor _,_
  field value  : A
        .proof : P value
open Refine public

-- The syntax declaration below is attached to Refine-syntax, to make it
-- easy to import Refine without the special syntax.

infix 2 Refine-syntax

Refine-syntax = Refine

syntax Refine-syntax A (λ x → P) = [ x ∈ A ∣ P ]

module _ {a b p q} {A : Set a} {B : Set b} {P : A → Set p} {Q : B → Set q} where

  map : (f : A → B) → (∀ {a} → P a → Q (f a)) → [ a ∈ A ∣ P a ] → [ b ∈ B ∣ Q b ]
  map f prf (a , p) = f a , prf p

module _ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} where

  refine : (∀ {a} → P a → Q a) → [ a ∈ A ∣ P a ] → [ a ∈ A ∣ Q a ]
  refine = map id

