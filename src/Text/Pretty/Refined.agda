module Text.Pretty.Refined where

import Level

open import Data.Erased as Erased hiding (module Erased) using (Erased)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product as Prod using (_×_; _,_; uncurry; proj₁; proj₂)

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

import Text.Pretty.Interface as I

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

  sized-Maybe : ∀ {a} {A : Set a} → {{_ : Sized A}} → Sized (Maybe A)
  sized-Maybe = record { size = maybe′ size 0 }

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
≤-Block {m} {n} m≤n = MaybeAll.map (Prod.map step (TreeAll.map step)) where

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

    pad : Maybe String
    pad with B.lastWidth x
    ... | 0 = nothing
    ... | l = just (replicate l ' ')

    size-pad : size pad ≡ B.lastWidth x
    size-pad with B.lastWidth x
    ... | 0         = refl
    ... | l@(suc _) = length-replicate l

    indent : Maybe String → String → String
    indent = maybe′ _++_ id

    size-indent : ∀ ma str → size (indent ma str) ≡ size ma + size str
    size-indent nothing    str = refl
    size-indent (just pad) str = length-++ pad str

    indents : Maybe String → Tree String → Tree String
    indents = maybe′ (Tree.map ∘ _++_) id

    size-indents : ∀ ma t → size (indents ma t) ≡ size t
    size-indents nothing    t = refl
    size-indents (just pad) t = Treeₚ.size-map (pad ++_) t

    unfold-indents : ∀ ma t → indents ma t ≡ Tree.map (indent ma) t
    unfold-indents nothing    t = sym (Treeₚ.map-id t)
    unfold-indents (just pad) t = refl

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
      (indents pad                    {-|-}       tl)          {------}
      , indent pad                    {-|-} (B.last y .value)  {-|-}
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
      rest   = indents pad tl
      ∣rest∣ = size-indents pad tl

    block : [ xs ∈ Block ∣ ∣ xs ∣≡ height ]
    block .value = vBlock
    block .proof = ⦇ isBlock (B.block x .proof) (B.block y .proof) ⦈
      where open Erased

    isLastLine : ∣ B.last x .value ∣≡ B.lastWidth x →
                 ∣ B.last y .value ∣≡ B.lastWidth y →
                 ∣ vLast ∣≡ lastWidth
    isLastLine ∣x∣ ∣y∣ with B.block y .value
    ... | [ nothing ]        = begin
      length (B.last x .value ++ B.last y .value)         ≡⟨ length-++ (B.last x .value) (B.last y .value) ⟩
      length (B.last x .value) + length (B.last y .value) ≡⟨ cong₂ _+_ ∣x∣ ∣y∣ ⟩
      B.lastWidth x + B.lastWidth y ∎ where open ≡-Reasoning
    ... | [ just (hd , tl) ] = begin
      length (indent pad (B.last y .value)) ≡⟨ size-indent pad (B.last y .value) ⟩
      size pad + length (B.last y .value)   ≡⟨ cong₂ _+_ size-pad ∣y∣ ⟩
      B.lastWidth x + B.lastWidth y         ∎ where

      open ≡-Reasoning

    last : [ s ∈ String ∣ ∣ s ∣≡ lastWidth ]
    last .value = vLast
    last .proof = ⦇ isLastLine (B.last x .proof) (B.last y .proof) ⦈
      where open Erased

    vMaxWidth : ℕ
    vMaxWidth = B.maxWidth x .value
              ⊔ (B.lastWidth x + B.maxWidth y .value)

    isMaxWidth₁ : B.lastWidth y ≤ B.maxWidth y .value →
                  lastWidth ≤ vMaxWidth
    isMaxWidth₁ p = begin
      lastWidth                           ≤⟨ +-monoʳ-≤ (B.lastWidth x) p ⟩
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
                     (subst (All≤ _) (sym $ unfold-indents pad tl)
                     $ TreeAll.map⁺ (indent pad) (TreeAll.map (indented _) ∣tl∣))

      where

      middle : ∣ B.last x .value ++ hd ∣≤ vMaxWidth
      middle = begin
        length (B.last x .value ++ hd)       ≡⟨ length-++ (B.last x .value) hd ⟩
        length (B.last x .value) + length hd ≡⟨ cong (_+ _) ∣x∣≡ ⟩
        B.lastWidth x + length hd            ≤⟨ +-monoʳ-≤ (B.lastWidth x) ∣hd∣ ⟩
        B.lastWidth x + B.maxWidth y .value  ≤⟨ n≤m⊔n _ _ ⟩
        vMaxWidth ∎ where open ≤-Reasoning

      indented : ∀ s → ∣ s ∣≤ B.maxWidth y .value → ∣ indent pad s ∣≤ vMaxWidth
      indented s ∣s∣ = begin
        size (indent pad s)                 ≡⟨ size-indent pad s ⟩
        size pad + length s                 ≡⟨ cong (_+ _) size-pad ⟩
        B.lastWidth x + length s            ≤⟨ +-monoʳ-≤ (B.lastWidth x) ∣s∣ ⟩
        B.lastWidth x + B.maxWidth y .value ≤⟨ n≤m⊔n (B.maxWidth x .value) _ ⟩
        vMaxWidth                           ∎ where open ≤-Reasoning

    maxWidth : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n block ]
    maxWidth .value = vMaxWidth
    maxWidth .proof =
      ⦇ _,_ ⦇ isMaxWidth₁ (map proj₁ (B.maxWidth y .proof)) ⦈
            ⦇ isMaxWidth₂ (B.last x .proof)
                          (map proj₁ (B.maxWidth x .proof))
                          (map proj₂ (B.maxWidth x .proof))
                          (map proj₂ (B.maxWidth y .proof))
            ⦈
      ⦈ where open Erased

  infixl 4 _<>_
  _<>_ : B → B → B
  x <> y = record { append x y }

  text : String → B
  text s = record
    { height    = 0
    ; block     = [ nothing ] , ⦇ refl ⦈
    ; lastWidth = width
    ; last      = s , ⦇ refl ⦈
    ; maxWidth  = width , ⦇ (≤-refl , nothing) ⦈
    } where width = length s; open Erased

  module flush (x : B) where

    height    = suc (B.height x)
    lastWidth = 0
    vMaxWidth = B.maxWidth x .value

    last : [ s ∈ String ∣ ∣ s ∣≡ lastWidth ]
    last = "" , ⦇ refl ⦈ where open Erased

    vBlock = the-block (B.block x .value) (B.last x .value) leaf

    isBlock : ∣ B.block x .value ∣≡ B.height x → ∣ vBlock ∣≡  height
    isBlock ∣x∣ = begin
      size vBlock                 ≡⟨ ∣the-block∣ (B.block x .value) (B.last x .value) leaf ⟩
      size (B.block x .value) + 1 ≡⟨ cong (_+ 1) ∣x∣ ⟩
      B.height x + 1              ≡⟨ +-comm (B.height x) 1 ⟩
      height                      ∎ where open ≡-Reasoning

    block : [ xs ∈ Block ∣ ∣ xs ∣≡ height ]
    block .value = vBlock
    block .proof = Erased.map isBlock $ B.block x .proof

    maxWidth : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n block ]
    maxWidth .value = B.maxWidth x .value
    maxWidth .proof = map (z≤n ,_) ⦇ All≤-the-block left middle right ⦈ where

      open Erased

      left : Erased (All≤ (value (B.maxWidth x)) (B.block x))
      left = map proj₂ (B.maxWidth x .proof)

      middle : Erased (∣ B.last x .value ∣≤ vMaxWidth)
      middle = pure (λ p q → begin
        length (B.last x .value) ≡⟨ p ⟩
        x .B.lastWidth           ≤⟨ q ⟩ -- B.maxWidth x .proof .proj₁ ⟩
        vMaxWidth                ∎)
        <*> B.last x .proof <*> (map proj₁ (B.maxWidth x .proof))
        where open ≤-Reasoning

      right : Erased (All≤ (value maxWidth) leaf)
      right = pure leaf

  flush : B → B
  flush x = record { flush x }

  render : B → String
  render x = unlines
    $ maybe′ (uncurry (λ hd tl → hd ∷ Tree.toList tl)) [] ∘′ content
    $ the-block (B.block x .value) (B.last x .value) leaf


instance

  layout-Refined : I.Layout B
  layout-Refined = record { layout }

module layouts where

  Bs = List B

  open import Category.Monad
  import Data.List.Categorical as Cat
  open import Data.Bool
  open import Agda.Builtin.Nat renaming (_<_ to _<?ᵇ_)
  open RawMonad (Cat.monad {Level.zero})
  open import Data.Maybe.Base
  import Data.List.NonEmpty as NE

  valid : B → Bool
  valid x = B.maxWidth x .value <?ᵇ 81

  infixr 5 _<>_
  _<>_ : Bs → Bs → Bs
  xs <> ys = List.boolFilter valid (I._<>_ <$> xs ⊛ ys)

  text : String → Bs
  text = List.boolFilter valid ∘ pure ∘ I.text

  flush : Bs → Bs
  flush = I.flush <$>_

  mostFrugal : Bs → B
  mostFrugal = maybe (NE.foldr₁ (minBy B.height) ∘′ uncurry NE._∷_) I.empty
             ∘′ List.uncons

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
