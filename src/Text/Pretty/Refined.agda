{-# OPTIONS --irrelevant-projections #-}
module Text.Pretty.Refined where

import Level
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product
open import Data.Tree.Binary as Tree using (Tree; leaf; node)
open import Data.Maybe.Base
import Data.Maybe.Relation.Unary.All as Maybe
import Data.List.Relation.Unary.All
import Data.Maybe.Relation.Unary.All
open import Data.String.Base as String
open import Data.String.Unsafe
open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Refinement as R
open import Utils

record Sized {a} (A : Set a) : Set a where
  field size : A → ℕ
  ∣_∣≡_ : A → ℕ → Set
  ∣ a ∣≡ n = size a ≡ n

  ∣_∣≤_ : A → ℕ → Set
  ∣ a ∣≤ n = size a ≤ n
open Sized {{...}}

record All (FA : Set) (A : Set) : Set₁ where
  field allOf : (A → Set) → (FA → Set)

  All≡ : {{s : Sized A}} → ℕ → FA → Set
  All≡ n = allOf (∣_∣≡ n)

  All≤ : {{s : Sized A}} → ℕ → FA → Set
  All≤ n = allOf (∣_∣≤ n)
open All {{...}}

record Block : Set where
  constructor [_]
  field content : Maybe (String × Tree String)
open Block

instance
  all-Maybe : ∀ {FA A} → {{_ : All FA A}} → All (Maybe FA) A
  all-Maybe = record { allOf = Maybe.All ∘′ allOf }

  all-Tree : ∀ {A} → All (Tree A) A
  all-Tree = record { allOf = Tree.All }

  all-Pair : ∀ {L R A} {{_ : All L A}} {{_ : All R A}} → All (L × R) A
  all-Pair = record { allOf = λ P → uncurry λ L R → allOf P L × allOf P R }

  all-Refine : ∀ {FA A P} {{_ : All FA A}} → All (Refine FA P) A
  all-Refine = record { allOf = λ P → allOf P ∘′ value }

  all-Refl : All String String
  all-Refl = record { allOf = id }

  all-Block : All Block String
  all-Block = record { allOf = λ P → allOf P ∘′ content }

instance

  sized-String : Sized String
  sized-String = record { size = String.length }

  sized-Tree : ∀ {a} {A : Set a} → Sized (Tree A)
  sized-Tree = record { size = Tree.size }

  sized-Block : Sized Block
  sized-Block = record { size = maybe′ (suc ∘ size ∘ proj₂) 0 ∘ content }

record B : Set where
  field
    height    : ℕ
    block     : [ xs ∈ Block ∣ ∣ xs ∣≡ height ]
  -- last line
    lastWidth : ℕ
    last      : [ s ∈ String ∣ ∣ s ∣≡ lastWidth ]
  -- max of all the widths
    maxWidth  : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n block ]

the-block : Block → String → Tree String → Block
the-block [ just (x , xs) ] y ys = [ just (x , node xs y ys) ]
the-block [ nothing       ] y ys = [ just (y , ys) ]

∣the-block∣ : ∀ b y ys → size (the-block b y ys) ≡ size b + suc (size ys)
∣the-block∣ [ just (x , xs) ] y ys = refl
∣the-block∣ [ nothing       ] y ys = refl

module layout where

  module append (x y : B) where

    height : ℕ
    height = (_+_ on B.height) x y

    lastWidth : ℕ
    lastWidth = (_+_ on B.lastWidth) x y

    vContent : Block × String
    vContent with B.block y .value .content
    ... | nothing        = B.block x .value
                         , B.last x .value ++ B.last y .value
    ... | just (hd , tl) = the-block
      {---------------------------------------}
      {-|-} (B.block x .value)            {-|-}
      {-|-}                  {----------------------------------------}
      {-|-} (B.last x .value {-|-} ++ {-|-}       hd)             {-|-}
      {--------------------------}    {-|-}                       {-|-}
      (Tree.map (indent ++_)          {-|-}       tl)          {------}
      , indent ++                     {-|-} B.last y .value    {-|-}
                                      {----------------------------}
      where indent = replicate (B.lastWidth x) ' '

    vblock = proj₁ vContent
    vlast  = proj₂ vContent

    isBlock : ∣ B.block x .value ∣≡ B.height x →
              ∣ B.block y .value ∣≡ B.height y →
              ∣ vblock ∣≡ height
    isBlock ∣x∣ ∣y∣ with B.block y .value
    ... | [ nothing ]        = begin
      size (B.block x .value) ≡⟨ ∣x∣ ⟩
      B.height x              ≡˘⟨ +-identityʳ (B.height x) ⟩
      B.height x + 0          ≡⟨ cong (_ +_) ∣y∣ ⟩
      B.height x + B.height y ∎ where open ≡-Reasoning
    ... | [ just (hd , tl) ] = begin
      size (the-block block middle rest) ≡⟨ ∣the-block∣ block middle rest ⟩
      size block + suc (size rest)       ≡⟨ cong ((size block +_) ∘′ suc) ∣rest∣ ⟩
      size block + suc (size tl)         ≡⟨ cong₂ _+_ ∣x∣ ∣y∣ ⟩
      B.height x + B.height y ∎  where

      open ≡-Reasoning
      block  = B.block x .value
      indent = replicate (B.lastWidth x) ' '
      middle = B.last x .value ++ hd
      rest   = Tree.map (indent ++_) tl
      ∣rest∣ = Tree.size-map (indent ++_) tl

    block : [ xs ∈ Block ∣ ∣ xs ∣≡ height ]
    block .value = vblock
    block .proof = isBlock (B.block x .proof) (B.block y .proof)

    isLastLine : ∣ B.last x .value ∣≡ B.lastWidth x →
                 ∣ B.last y .value ∣≡ B.lastWidth y →
                 ∣ vlast ∣≡ lastWidth
    isLastLine ∣x∣ ∣y∣ with B.block y .value
    ... | [ nothing ]        = begin
      length (B.last x .value ++ B.last y .value)         ≡⟨ length-++ (B.last x .value) (B.last y .value) ⟩
      length (B.last x .value) + length (B.last y .value) ≡⟨ cong₂ _+_ ∣x∣ ∣y∣ ⟩
      B.lastWidth x + B.lastWidth y ∎ where open ≡-Reasoning
    ... | [ just (hd , tl) ] = begin
      length (indent ++ B.last y .value)       ≡⟨ length-++ indent (B.last y .value) ⟩
      length indent + length (B.last y .value) ≡⟨ cong₂ _+_ (length-replicate (B.lastWidth x)) ∣y∣ ⟩
      B.lastWidth x + B.lastWidth y            ∎ where

      open ≡-Reasoning
      indent = replicate (B.lastWidth x) ' '

    last : [ s ∈ String ∣ ∣ s ∣≡ lastWidth ]
    last .value = vlast
    last .proof = isLastLine (B.last x .proof) (B.last y .proof)

    vMaxWidth : ℕ
    vMaxWidth = B.maxWidth x .value ⊔ (B.lastWidth x + B.maxWidth y .value)

{-
    .isMaxWidth : lastWidth ≤ vMaxWidth
    isMaxWidth = P.begin
        lastWidth
          P.∼⟨ +-monoʳ-≤ (B.lastWidth x) (B.maxWidth y .proof) ⟩
        B.lastWidth x + B.maxWidth y .value
          P.∼⟨ n≤m⊔n (B.maxWidth x .value) _ ⟩
        B.maxWidth x .value ⊔ (B.lastWidth x + B.maxWidth y .value)
          P.∎

    maxWidth : [ n ∈ ℕ ∣ lastWidth ≤ n ]
    maxWidth = vMaxWidth , isMaxWidth

    .isMainBlock₂ : All ((_≤ vMaxWidth) ∘ Slength) vMainBlock
    isMainBlock₂ with initLast (B.mainBlock y .value)
    ... | []        = All.map (flip ≤-trans (m≤m⊔n _ _)) (proj₂ (B.mainBlock x .proof))
    ... | tl ∷ʳ' hd = ++⁺ (All.map (λ {s} → pry {s}) (++⁻ˡ tl (proj₂ (B.mainBlock y .proof))))
                    $ prm
                    ∷ All.map (flip ≤-trans (m≤m⊔n _ _)) (proj₂ (B.mainBlock x .proof)) where

      .pry : (_≤ B.maxWidth y .value) ∘ Slength ⊆ (_≤ vMaxWidth) ∘ Slength
      pry {s} p = P.begin
        Slength s                           P.∼⟨ p ⟩
        B.maxWidth y .value                 P.∼⟨ n≤m+n (B.lastWidth x) _ ⟩
        B.lastWidth x + B.maxWidth y .value P.∼⟨ n≤m⊔n (B.maxWidth x .value) _ ⟩
        vMaxWidth                           P.∎

      .prm : Slength (B.lastLine x .value String.++ hd) ≤ vMaxWidth
      prm = P.begin
        Slength (B.lastLine x .value String.++ hd)
          P.≈⟨ Slength-++ (B.lastLine x .value) hd ⟩
        Slength (B.lastLine x .value) + Slength hd
          P.≈⟨ cong (_+ _) (B.lastLine x .proof) ⟩
        B.lastWidth x + Slength hd
          P.∼⟨ +-monoʳ-≤ (B.lastWidth x) ([ hd ]⁻ (++⁻ʳ tl (proj₂ (B.mainBlock y .proof)))) ⟩
        B.lastWidth x + B.maxWidth y .value
          P.∼⟨ n≤m⊔n (B.maxWidth x .value) _ ⟩
        vMaxWidth P.∎

    mainBlock : Block height vMaxWidth
    mainBlock = vMainBlock , (isMainBlock₁ , isMainBlock₂)

  infixl 4 _<>_
  _<>_ : B → B → B
  x <> y = record { append x y }

  text : String → B
  text s = mkB 0 (Slength s) (Slength s , ≤-refl) (s , refl) ([] , refl , [])

  flush : B → B
  B.height    (flush x) = suc (B.height x)
  B.lastWidth (flush x) = 0
  B.maxWidth  (flush x) = refine (λ _ → z≤n) (B.maxWidth x)
  B.lastLine  (flush x) = "" , refl
  B.mainBlock (flush x) = (B.lastLine x .value ∷ B.mainBlock x .value)
                        , cong suc (proj₁ (B.mainBlock x .proof))
                        , (prf ∷ proj₂ (B.mainBlock x .proof)) where

    .prf : Slength (B.lastLine x .value) ≤ B.maxWidth x .value
    prf = P.begin
      Slength (B.lastLine x .value) P.≈⟨ B.lastLine x .proof ⟩
      x .B.lastWidth                P.∼⟨ B.maxWidth x .proof ⟩
      B.maxWidth x .value           P.∎

  render : B → String
  render x = unlines $ List.reverse
           $ B.lastLine x .value
           ∷ B.mainBlock x .value

instance

  layout-Refined : I.Layout B
  layout-Refined = record { layout }


module layouts where

  Bs = List B

  open import Data.Bool
  open import Agda.Builtin.Nat renaming (_<_ to _<?ᵇ_)
  open RawMonad (Cat.monad {L.zero})
  open import Data.Maybe.Base
  import Data.List.NonEmpty as NE

  valid : B → Bool
  valid x = B.maxWidth x .value <?ᵇ 81

  infixr 5 _<>_
  _<>_ : Bs → Bs → Bs
  xs <> ys = boolFilter valid (I._<>_ <$> xs ⊛ ys)

  text : String → Bs
  text = boolFilter valid ∘ pure ∘ I.text

  flush : Bs → Bs
  flush = I.flush <$>_

  mostFrugal : Bs → B
  mostFrugal = maybe (NE.foldr₁ (minBy B.height)) I.empty
             ∘′ uncons

  render : Bs → String
  render = I.render ∘′ mostFrugal

instance

  layout-Refineds : I.Layout layouts.Bs
  layout-Refineds = record { layouts }


module doc where

  open layouts

  _<|>_ : Bs → Bs → Bs
  x <|> y = x List.++ y

  fail : Bs
  fail = []

instance

  doc-Refineds : I.Doc layouts.Bs
  doc-Refineds = record { doc }
-}
