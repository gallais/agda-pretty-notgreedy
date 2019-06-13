module Data.Tree.Binary.Relation.Unary.All where

open import Level
open import Data.Tree.Binary as Tree using (Tree; leaf; node)
open import Relation.Unary

private
  variable
    a b p q : Level
    A : Set a
    B : Set b
    P : A → Set p
    Q : A → Set q

data All {A : Set a} (P : A → Set p) : Tree A → Set (a ⊔ p) where
  leaf : All P leaf
  node : ∀ {l m r} → All P l → P m → All P r → All P (node l m r)

map : ∀[ P ⇒ Q ] → ∀[ All P ⇒ All Q ]
map f leaf         = leaf
map f (node l m r) = node (map f l) (f m) (map f r)

map⁺ : (f : A → B) → ∀[ All (f ⊢ P) ⇒ Tree.map f ⊢ All P ]
map⁺ f leaf         = leaf
map⁺ f (node l m r) = node (map⁺ f l) m (map⁺ f r)
