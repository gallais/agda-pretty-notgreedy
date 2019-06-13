{-# OPTIONS --irrelevant-projections #-}

module Text.Pretty.Refined where

import Level

open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product as Product using (_×_; _,_; uncurry; proj₁; proj₂)

open import Data.Tree.Binary as Tree using (Tree; leaf; node)
open import Data.Tree.Binary.Relation.Unary.All as TreeAll using (leaf; node)
import Data.Tree.Binary.Properties as Treeₚ

open import Data.Maybe.Base as Maybe using (Maybe; nothing; just; maybe′)
open import Data.Maybe.Relation.Unary.All as MaybeAll using (nothing; just)

open import Data.String.Base as String
open import Data.String.Unsafe
open import Function
open import Relation.Unary using (IUniversal; _⇒_)
open import Relation.Binary.PropositionalEquality

open import Data.Refinement hiding (map)
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
  all-Maybe = record { allOf = MaybeAll.All ∘′ allOf }

  all-Tree : ∀ {A} → All (Tree A) A
  all-Tree = record { allOf = TreeAll.All }

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

≤-Block : ∀ {m n} {b : Block} → m ≤ n → All≤ m b → All≤ n b
≤-Block {m} {n} m≤n = MaybeAll.map (Product.map step (TreeAll.map step)) where

  step : ∀ {p} → p ≤ m → p ≤ n
  step = flip ≤-trans m≤n

All≤-the-block : ∀ {l m r n} →
  All≤ n l → All≤ n m → All≤ n r → All≤ n (the-block l m r)
All≤-the-block nothing           py pys = just (py , pys)
All≤-the-block (just (px , pxs)) py pys = just (px , node pxs py pys)

module layout where

  module append (x y : B) where

    height : ℕ
    height = (_+_ on B.height) x y

    lastWidth : ℕ
    lastWidth = (_+_ on B.lastWidth) x y

    indent : String
    indent = replicate (B.lastWidth x) ' '

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

    vBlock = proj₁ vContent
    vLast  = proj₂ vContent

    isBlock : ∣ B.block x .value ∣≡ B.height x →
              ∣ B.block y .value ∣≡ B.height y →
              ∣ vBlock ∣≡ height
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
      middle = B.last x .value ++ hd
      rest   = Tree.map (indent ++_) tl
      ∣rest∣ = Treeₚ.size-map (indent ++_) tl

    block : [ xs ∈ Block ∣ ∣ xs ∣≡ height ]
    block .value = vBlock
    block .proof = isBlock (B.block x .proof) (B.block y .proof)

    isLastLine : ∣ B.last x .value ∣≡ B.lastWidth x →
                 ∣ B.last y .value ∣≡ B.lastWidth y →
                 ∣ vLast ∣≡ lastWidth
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

    last : [ s ∈ String ∣ ∣ s ∣≡ lastWidth ]
    last .value = vLast
    last .proof = isLastLine (B.last x .proof) (B.last y .proof)

    vMaxWidth : ℕ
    vMaxWidth = B.maxWidth x .value
              ⊔ (B.lastWidth x + B.maxWidth y .value)

    isMaxWidth₁ : B.lastWidth y ≤ B.maxWidth y .value →
                  lastWidth ≤ vMaxWidth
    isMaxWidth₁ ∣y∣ = begin
      lastWidth                           ≤⟨ +-monoʳ-≤ (B.lastWidth x) ∣y∣ ⟩
      B.lastWidth x + B.maxWidth y .value ≤⟨ n≤m⊔n _ _ ⟩
      vMaxWidth                           ∎ where open ≤-Reasoning

    isMaxWidth₂ : ∣ B.last x .value ∣≡ B.lastWidth x →
                  B.lastWidth x ≤ B.maxWidth x .value →
                  All≤ (B.maxWidth x .value) (B.block x .value) →
                  All≤ (B.maxWidth y .value) (B.block y .value) →
                  All≤ vMaxWidth vBlock
    isMaxWidth₂ ∣x∣≡ ∣x∣≤ ∣xs∣ ∣ys∣ with B.block y .value
    ... | [ nothing ]        = ≤-Block (m≤m⊔n _ _) ∣xs∣
    isMaxWidth₂ ∣x∣≡ ∣x∣≤ ∣xs∣ (just (∣hd∣ , ∣tl∣)) | [ just (hd , tl) ] =
      All≤-the-block (≤-Block (m≤m⊔n _ _) ∣xs∣)
                     middle
                     (TreeAll.map⁺ (indent ++_) (TreeAll.map (indented _) ∣tl∣))

      where

      middle : ∣ B.last x .value ++ hd ∣≤ vMaxWidth
      middle = begin
        length (B.last x .value ++ hd)       ≡⟨ length-++ (B.last x .value) hd ⟩
        length (B.last x .value) + length hd ≡⟨ cong (_+ _) ∣x∣≡ ⟩
        B.lastWidth x + length hd            ≤⟨ +-monoʳ-≤ (B.lastWidth x) ∣hd∣ ⟩
        B.lastWidth x + B.maxWidth y .value  ≤⟨ n≤m⊔n _ _ ⟩
        vMaxWidth ∎ where open ≤-Reasoning

      indented : ∀ s → ∣ s ∣≤ B.maxWidth y .value → ∣ indent ++ s ∣≤ vMaxWidth
      indented s ∣s∣ = begin
        size (indent ++ s)                  ≡⟨ length-++ indent s ⟩
        length indent + length s            ≡⟨ cong (_+ _) (length-replicate (B.lastWidth x)) ⟩
        B.lastWidth x + length s            ≤⟨ +-monoʳ-≤ (B.lastWidth x) ∣s∣ ⟩
        B.lastWidth x + B.maxWidth y .value ≤⟨ n≤m⊔n (B.maxWidth x .value) _ ⟩
        vMaxWidth                           ∎ where open ≤-Reasoning

    maxWidth : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n block ]
    maxWidth .value = vMaxWidth
    maxWidth .proof = isMaxWidth₁ (B.maxWidth y .proof .proj₁)
                    , isMaxWidth₂ (B.last x .proof) (B.maxWidth x .proof .proj₁)
                                  (B.maxWidth x .proof .proj₂) (B.maxWidth y .proof .proj₂)

  infixl 4 _<>_
  _<>_ : B → B → B
  x <> y = record { append x y }

  text : String → B
  text s = record
    { height    = 0
    ; block     = [ nothing ] , refl
    ; lastWidth = width
    ; last      = s , refl
    ; maxWidth  = width , ≤-refl , nothing
    } where width = length s

  module flush (x : B) where

    height    = suc (B.height x)
    lastWidth = 0
    vMaxWidth = B.maxWidth x .value

    last : [ s ∈ String ∣ ∣ s ∣≡ lastWidth ]
    last = "" , refl

    vBlock = the-block (B.block x .value) (B.last x .value) leaf

    isBlock : ∣ B.block x .value ∣≡ B.height x → ∣ vBlock ∣≡  height
    isBlock ∣x∣ = begin
      size vBlock                 ≡⟨ ∣the-block∣ (B.block x .value) (B.last x .value) leaf ⟩
      size (B.block x .value) + 1 ≡⟨ cong (_+ 1) ∣x∣ ⟩
      B.height x + 1              ≡⟨ +-comm (B.height x) 1 ⟩
      height                      ∎ where open ≡-Reasoning

    block : [ xs ∈ Block ∣ ∣ xs ∣≡ height ]
    block .value = vBlock
    block .proof = isBlock (B.block x .proof)

    maxWidth : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n block ]
    maxWidth .value = B.maxWidth x .value
    maxWidth .proof = z≤n , All≤-the-block (B.maxWidth x .proof .proj₂) middle leaf where

      middle : ∣ B.last x .value ∣≤ vMaxWidth
      middle = begin
        length (B.last x .value) ≡⟨ B.last x .proof ⟩
        x .B.lastWidth           ≤⟨ B.maxWidth x .proof .proj₁ ⟩
        vMaxWidth                ∎ where open ≤-Reasoning

  flush : B → B
  flush x = record { flush x }

  render : B → String
  render x = unlines
    $ maybe′ (uncurry (λ hd tl → hd ∷ Tree.toList tl)) [] ∘′ content
    $ the-block (B.block x .value) (B.last x .value) leaf


{-
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
