module Text.Pretty.NonEmpty where

open import Level                 as L
open import Category.Monad
open import Data.List.Base        as List
open import Data.List.All         as All
open import Data.List.Categorical as Cat
open import Data.List.NonEmpty    as NE
open import Data.Maybe.Base       as Maybe
open import Data.Nat
open import Data.Product
open import Data.String.Base      as String
open import Function
open import Relation.Unary
import Text.Pretty.Interface      as I
open import Utils

module layout where

  L = List⁺ String

  text : String → L
  text = NE.[_]

  infixl 4 _<>_
  _<>_ : L → L → L
  xs <> y ∷ ys with snocView xs
  ... | xs₀ ∷ʳ′ x =
    let indent = String.replicate (String.length x) ' ' in
    xs₀ ++⁺ (x String.++ y) ∷ List.map (indent String.++_) ys

  flush : L → L
  flush = _⁺∷ʳ ""

  render : L → String
  render = unlines ∘ NE.toList

instance

  layout-String⁺ : I.Layout layout.L
  layout-String⁺ = record { layout }

module layouts where

  D = List layout.L

  open RawMonad (Cat.monad {L.zero})

  text : String → D
  text = List.[_] ∘ I.text

  _<>_ : D → D → D
  xs <> ys = I._<>_ <$> xs ⊛ ys

  flush : D → D
  flush  = List.map I.flush

  visible : Decidable (All.All ((_≤ 80) ∘ String.length) ∘ NE.toList)
  visible = All.all ((_≤? 80) ∘ String.length) ∘ NE.toList

  mostFrugal : D → layout.L
  mostFrugal = proj₁
             ∘′ maybe (NE.foldr₁ (minBy proj₂)) (I.empty , 0)
             ∘′ NE.fromList
             ∘′ List.map < id , NE.length >

  render : D → String
  render = I.render ∘′ mostFrugal ∘′ filter visible

instance

  layout-String⁺s : I.Layout layouts.D
  layout-String⁺s = record { layouts }

module doc where

  open layouts

  _<|>_ : D → D → D
  x <|> y = x List.++ y

  fail : D
  fail = []

instance

  doc-String⁺s : I.Doc layouts.D
  doc-String⁺s = record { doc }
