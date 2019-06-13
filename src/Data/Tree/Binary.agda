module Data.Tree.Binary where

open import Level
open import Data.List.Base using (List)
open import Data.DifferenceList as DiffList using (DiffList; []; _∷_; _++_)
open import Function

data Tree {a} (A : Set a) : Set a where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A

private
  variable
    a b : Level
    A : Set a
    B : Set b

map : (A → B) → Tree A → Tree B
map f leaf         = leaf
map f (node l m r) = node (map f l) (f m) (map f r)

toDiffList : Tree A → DiffList A
toDiffList leaf         = []
toDiffList (node l m r) = toDiffList l ++ m ∷ toDiffList r

toList : Tree A → List A
toList = DiffList.toList ∘′ toDiffList
