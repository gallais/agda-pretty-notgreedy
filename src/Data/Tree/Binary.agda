{-# OPTIONS --without-K --safe #-}

module Data.Tree.Binary where

open import Level using (Level; _⊔_)
open import Data.List.Base using (List)
open import Data.DifferenceList as DiffList using (DiffList; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Function
open import Relation.Binary.PropositionalEquality

private
  variable
    a b : Level
    A : Set a
    B : Set b

data Tree (A : Set a) : Set a where
  leaf : Tree A
  node : Tree A → A → Tree A → Tree A

map : (A → B) → Tree A → Tree B
map f leaf         = leaf
map f (node l m r) = node (map f l) (f m) (map f r)

size : Tree A → ℕ
size leaf         = 0
size (node l m r) = size l + suc (size r)

toDiffList : Tree A → DiffList A
toDiffList leaf         = []
toDiffList (node l m r) = toDiffList l ++ m ∷ toDiffList r

toList : Tree A → List A
toList = DiffList.toList ∘′ toDiffList
