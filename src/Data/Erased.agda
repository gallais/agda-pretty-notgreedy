module Data.Erased where

open import Level using (Level)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

record Erased (A : Set a) : Set a where
  constructor [_]
  field .erased : A
open Erased public

pure : A → Erased A
pure = [_]

map : (A → B) → Erased A → Erased B
map f [ a ] = [ f a ]

infixl 4 _<*>_
_<*>_ : Erased (A → B) → Erased A → Erased B
[ f ] <*> [ a ] = [ f a ]

infixl 1 _>>=_
_>>=_ : Erased A → (.A → Erased B) → Erased B
[ a ] >>= f = f a
