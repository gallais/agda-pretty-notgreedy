module Text.Pretty.Refined where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.List.Base as List
open import Data.List.Properties
open import Data.String.Base as String
open import Data.Vec as Vec
open import Data.Vec.All as All
open import Data.Vec.All.Properties
open import Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality

import Text.Pretty.Interface as I
open import Data.Refinement as R
open import Utils

import Relation.Binary.PreorderReasoning
module P = Relation.Binary.PreorderReasoning ≤-preorder
open import Relation.Binary.PropositionalEquality
module E = Relation.Binary.PropositionalEquality.≡-Reasoning

Block : ℕ → ℕ → Set
Block m n = [ xs ∈ Vec String m ∣ All ((_≤ n) ∘ Slength) xs ]

record B : Set where
  constructor mkB
  field height     : ℕ
        lastWidth  : ℕ
        maxWidth   : [ n ∈ ℕ      ∣ lastWidth ≤ n         ]
        lastLine   : [ s ∈ String ∣ Slength s ≡ lastWidth ]
        mainBlock  : Block height (maxWidth .value)

module layout where

  module append (x y : B) where

    height : ℕ
    height = B.height y + suc (B.height x)

    lastWidth : ℕ
    lastWidth = (_+_ on B.lastWidth) x y

    vlastLine : String
    vlastLine = Sreplicate (B.lastWidth x) ' ' String.++ B.lastLine y .value

    .isLastLine : Slength vlastLine ≡ lastWidth
    isLastLine = E.begin
      Slength vlastLine E.≡⟨ cong length (toList-++ (Sreplicate (B.lastWidth x) ' ') _) ⟩
      _  E.≡⟨ length-++ (String.toList (Sreplicate (B.lastWidth x) ' ')) ⟩
      _  E.≡⟨ cong₂ _+_ (Slength-replicate (B.lastWidth x)) (B.lastLine y .proof) ⟩
      lastWidth E.∎

    lastLine : [ s ∈ String ∣ Slength s ≡ lastWidth ]
    lastLine = vlastLine , isLastLine

    vMaxWidth : ℕ
    vMaxWidth = B.maxWidth x .value ⊔ (B.lastWidth x + B.maxWidth y .value)

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

    vMainBlock : Vec String height
    vMainBlock = B.mainBlock y .value Vec.++ B.lastLine x .value ∷ B.mainBlock x .value

    .isMainBlock : All ((_≤ vMaxWidth) ∘ Slength) vMainBlock
    isMainBlock = All-++⁺ (All.map (λ {s} → pry {s}) (B.mainBlock y .proof))
                          (prm ∷ (All.map (λ {s} → prx {s}) (B.mainBlock x .proof))) where

      .pry : (_≤ B.maxWidth y .value) ∘ Slength ⊆ (_≤ vMaxWidth) ∘ Slength
      pry {s} p = P.begin
        Slength s                           P.∼⟨ p ⟩
        B.maxWidth y .value                 P.∼⟨ n≤m+n (B.lastWidth x) _ ⟩
        B.lastWidth x + B.maxWidth y .value P.∼⟨ n≤m⊔n (B.maxWidth x .value) _ ⟩
        vMaxWidth                           P.∎

      .prm : Slength (B.lastLine x .value) ≤ vMaxWidth
      prm = P.begin
        Slength (B.lastLine x .value)       P.≈⟨ B.lastLine x .proof ⟩
        B.lastWidth x                       P.∼⟨ m≤m+n (B.lastWidth x) (B.maxWidth y .value) ⟩
        B.lastWidth x + B.maxWidth y .value P.∼⟨ n≤m⊔n (B.maxWidth x .value) _ ⟩
        vMaxWidth                           P.∎

      .prx : ∀ {s} → Slength s ≤ B.maxWidth x .value → Slength s ≤ vMaxWidth
      prx {s} p = P.begin
        Slength s            P.∼⟨ p ⟩
        B.maxWidth x .value  P.∼⟨ m≤m⊔n _ _ ⟩
        vMaxWidth            P.∎

    mainBlock : Block height vMaxWidth
    mainBlock = vMainBlock , isMainBlock

  infixr 5 _<>_
  _<>_ : B → B → B
  x <> y = record { append x y }

  text : String → B
  text s = mkB 0 (Slength s) (Slength s , ≤-refl) (s , refl) ([] , [])

  flush : B → B
  B.height    (flush x) = suc (B.height x)
  B.lastWidth (flush x) = 0
  B.maxWidth  (flush x) = refine (λ _ → z≤n) (B.maxWidth x)
  B.lastLine  (flush x) = "" , refl
  B.mainBlock (flush x) = (B.lastLine x .value ∷ B.mainBlock x .value)
                        , (prf ∷ B.mainBlock x .proof) where

    .prf : Slength (B.lastLine x .value) ≤ B.maxWidth x .value
    prf = P.begin
      Slength (B.lastLine x .value) P.≈⟨ B.lastLine x .proof ⟩
      x .B.lastWidth                P.∼⟨ B.maxWidth x .proof ⟩
      B.maxWidth x .value           P.∎

  render : B → String
  render x = unlines $ List.reverse
           $ B.lastLine x .value
           ∷ Vec.toList (B.mainBlock x .value)

instance

  layout-Refined : I.Layout B
  layout-Refined = record { layout }
