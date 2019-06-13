module Text.Pretty.Refined where

import Level
open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product
open import Data.Tree.Binary as Tree
open import Data.Maybe.Base
import Data.List.Relation.Unary.All
import Data.Maybe.Relation.Unary.All
open import Data.String.Base as String
open import Function
open import Relation.Binary.PropositionalEquality

open import Data.Refinement as R

import Relation.Binary.PreorderReasoning
module P = Relation.Binary.PreorderReasoning ≤-preorder
open import Relation.Binary.PropositionalEquality
module E = Relation.Binary.PropositionalEquality.≡-Reasoning

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

instance
  all-Maybe : ∀ {A} → All (Maybe A) A
  all-Maybe = record { allOf = Data.Maybe.Relation.Unary.All.All }

  all-List : ∀ {A} → All (Tree A) A
  all-List = record { allOf = {!!} }

  all-Pair : ∀ {L R A} {{_ : All L A}} {{_ : All R A}} → All (L × R) A
  all-Pair = {!!}

  all-Refine : ∀ {F A P} {{_ : All F A}} → All (Refine F P) A
  all-Refine = record { allOf = λ P → allOf P ∘′ value }

instance

  sized-String : Sized String
  sized-String = record { size = String.length }

Block : Set
Block = Maybe (String × Tree String)

record B : Set where
  field
    height    : ℕ
    block     : [ xs ∈ Block ∣ {!!} ] -- ∣ xs ∣≡ height ]
  -- last line
    lastWidth : ℕ
    last      : [ s ∈ String ∣ ∣ s ∣≡ lastWidth ]
  -- max of all the widths
    maxWidth  : [ n ∈ ℕ ∣ lastWidth ≤ n × All≤ n block ]

the-block : Block → String → Tree String → Block
the-block (just (x , xs)) y ys = just (x , node xs y ys)
the-block nothing         y ys = just (y , ys)

module layout where

  module append (x y : B) where

    height : ℕ
    height = (_+_ on B.height) y x

    lastWidth : ℕ
    lastWidth = (_+_ on B.lastWidth) x y

    vContent : Maybe (String × Tree String) × String
    vContent with B.block y .value
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

    vmain = proj₁ vContent
    vlast = proj₂ vContent

{-
    .isLastLine : Slength vLastLine ≡ lastWidth
    isLastLine with initLast (B.mainBlock y .value)
    ... | []        = E.begin
      Slength (B.lastLine x .value String.++ B.lastLine y .value)
        E.≡⟨ cong length (toList-++ (B.lastLine x .value) (B.lastLine y .value)) ⟩
      length (toList (B.lastLine x .value) List.++ toList (B.lastLine y .value))
        E.≡⟨ length-++ (toList (B.lastLine x .value)) ⟩
      length (toList (B.lastLine x .value)) + length (toList (B.lastLine y .value))
        E.≡⟨ cong₂ _+_ (B.lastLine x .proof) (B.lastLine y .proof) ⟩
      x .B.lastWidth + y .B.lastWidth
        E.∎
    ... | tl ∷ʳ' hd = E.begin
      Slength (Sreplicate (B.lastWidth x) ' ' String.++ B.lastLine y .value)
        E.≡⟨ cong length (toList-++ (Sreplicate (B.lastWidth x) ' ') (B.lastLine y .value)) ⟩
      length (toList (Sreplicate (B.lastWidth x) ' ') List.++ toList (B.lastLine y .value))
        E.≡⟨ length-++ (toList (Sreplicate (B.lastWidth x) ' ')) ⟩
      length (toList (Sreplicate (B.lastWidth x) ' ')) + length (toList (B.lastLine y .value))
        E.≡⟨ cong₂ _+_ (Slength-replicate (B.lastWidth x)) (B.lastLine y .proof) ⟩
      B.lastWidth x + y .B.lastWidth
        E.∎

    lastLine : [ s ∈ String ∣ Slength s ≡ lastWidth ]
    lastLine = vLastLine , isLastLine
-}
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

    .isMainBlock₁ : List.length vMainBlock ≡ height
    isMainBlock₁ with initLast (B.mainBlock y .value)
    ... | []        = E.begin
      length (B.mainBlock x .value)
        E.≡⟨ cong₂ _+_ (proj₁ (B.mainBlock y .proof)) (proj₁ (B.mainBlock x .proof)) ⟩
      B.height y + B.height x
        E.∎
    ... | tl ∷ʳ' hd = E.begin
      length (tl List.++ _ ∷ B.mainBlock x .value)
        E.≡⟨ length-++ tl ⟩
      length tl + (1 + length (B.mainBlock x .value))
        E.≡⟨ sym (+-assoc (length tl) 1 _) ⟩
      length tl + 1 + length (B.mainBlock x .value)
        E.≡⟨ cong (_+ _) (sym (length-++ tl {List.[ hd ]})) ⟩
      length (tl ∷ʳ hd) + length (B.mainBlock x .value)
        E.≡⟨ cong₂ _+_ (proj₁ (B.mainBlock y .proof)) (proj₁ (B.mainBlock x .proof)) ⟩
      B.height y + B.height x
        E.∎

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
