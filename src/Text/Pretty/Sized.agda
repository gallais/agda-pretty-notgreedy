module Text.Pretty.Sized where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.String as String using (String)
import Data.List.Base as List
import Data.List.NonEmpty as NE
open import Data.Char.Base
open import Data.Vec as Vec
open import Data.BoundedVec as BVec
open import Function
open import Utils
import Text.Pretty.Interface  as I
import Text.Pretty.NonEmpty   as NE

open import Relation.Binary.PreorderReasoning ≤-preorder

record M : Set where
  constructor mkM
  field height     : ℕ
        lastWidth  : ℕ
        maxWidth   : ℕ
        isMaxWidth : lastWidth ≤ maxWidth
        lastLine   : Vec Char lastWidth
        content    : Vec (BoundedVec Char maxWidth) height

module layout where

  infixr 5 _<>_
  _<>_ : M → M → M
  M.height     (x <> y) = M.height y + M.height x
  M.lastWidth  (x <> y) = (_+_ on M.lastWidth) x y
  M.maxWidth   (x <> y) = M.maxWidth x ⊔ (M.lastWidth x + M.maxWidth y)
  M.isMaxWidth (x <> y) = begin
    M.lastWidth x + M.lastWidth y ∼⟨ +-monoʳ-≤ (M.lastWidth x) (M.isMaxWidth y) ⟩
    M.lastWidth x + M.maxWidth y  ∼⟨ n≤m⊔n (M.maxWidth x) _ ⟩
    M.maxWidth x ⊔ (M.lastWidth x + M.maxWidth y) ∎
  M.lastLine   (x <> y) = replicate {n = M.lastWidth x} ' ' ++ M.lastLine y
  M.content    (x <> y) = {!!}


  text : String → M
  text s = mkM 0 _ _ ≤-refl (String.toVec s) Vec.[]

  flush : M → M
  M.height     (flush x) = suc (M.height x)
  M.lastWidth  (flush x) = 0
  M.maxWidth   (flush x) = M.maxWidth x
  M.isMaxWidth (flush x) = z≤n
  M.lastLine   (flush x) = Vec.[]
  M.content    (flush x) = {!!} Vec.∷ M.content x

  render : M → String
  render x = String.unlines $ List.reverse
           $ SfromVec (M.lastLine x)
           List.∷ List.map SfromBoundedVec (Vec.toList (M.content x))

instance

  layout-Size : I.Layout M
  layout-Size = record { layout }
