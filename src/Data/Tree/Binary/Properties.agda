module Data.Tree.Binary.Properties where

open import Level using (Level)
open import Data.Nat.Base using (suc; _+_)
open import Data.Tree.Binary
open import Relation.Binary.PropositionalEquality

private
  variable
    a b : Level
    A : Set a
    B : Set b

size-map : ∀ (f : A → B) t → size (map f t) ≡ size t
size-map f leaf         = refl
size-map f (node l m r) = cong₂ (λ l r → l + suc r) (size-map f l) (size-map f r)
