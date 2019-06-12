module Text.Pretty.Interface where

open import Data.Nat.Base
open import Data.List.Base
open import Data.String.Base as String

record Layout {ℓ} (d : Set ℓ) : Set ℓ where
  infixl 4 _<>_
  infixr 6 _$$_
  field text   : String → d
        _<>_   : d → d → d
        flush  : d → d
        render : d → String

  spaces : ℕ → d
  spaces n = text (String.replicate n ' ')

  empty : d
  empty = spaces 0

  space = spaces 1

  _<+>_ : d → d → d
  x <+> y = x <> space <> y

  _$$_ : d → d → d
  x $$ y = flush x <> y

  foldDoc : (d → d → d) → List d → d
  foldDoc _ []       = empty
  foldDoc _ (x ∷ []) = x
  foldDoc f (x ∷ xs) = f x (foldDoc f xs)

  hsep vcat : List d → d
  hsep = foldDoc _<+>_
  vcat = foldDoc _$$_

open Layout {{...}} public

record Doc {ℓ} (d : Set ℓ) : Set ℓ where
  infixr 3 _<|>_
  field {{layout}} : Layout d
        _<|>_      : d → d → d
        fail       : d

  sep : List d → d
  sep [] = empty
  sep xs = hsep xs <|> vcat xs

open Doc {{...}} public
