module Text.Pretty.Interface where

open import Data.Char.Base   using (Char)
open import Data.List.Base   using (List; []; _∷_)
open import Data.Nat.Base    using (ℕ)
open import Data.String.Base

record Layout {ℓ} (d : Set ℓ) : Set ℓ where
  infixl 4 _<>_
  infixr 6 _$$_
  field text   : String → d
        _<>_   : d → d → d
        flush  : d → d
        render : d → String

  spaces : ℕ → d
  spaces n = text (replicate n ' ')

  empty : d
  empty = text ""

  char : Char → d
  char c = text (fromList (c ∷ []))

  semi colon comma space dot : d
  semi = char ';'; colon = char ':'
  comma = char ','; space = char ' '; dot = char '.'

  backslash forwardslash equal : d
  backslash = char '\\'; forwardslash = char '/'; equal = char '='

  squote dquote : d
  squote = char '\''; dquote = char '"'

  lparen rparen langle rangle lbrace rbrace lbracket rbracket : d
  lparen = char '('; rparen = char ')'
  langle = char '<'; rangle = char '>'
  lbrace = char '{'; rbrace = char '}'
  lbracket = char '['; rbracket = char ']'

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
