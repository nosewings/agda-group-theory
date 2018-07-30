module Base.List.Sublist where

open import Base.Type
open import Base.Relation
open import Base.WellFounded
open import Base.Nat
open import Base.List.Core

module _ {ℓ} {A : Type ℓ} where

  infixr 5 _∷_ _∺_
  infix  4 _≼_

  data _≼_ : Relation ℓ (List A) where
    [] : [] ≼ []
    _∺_ : ∀ y {xs ys} → xs ≼ ys → xs ≼ (y ∷ ys)
    _∷_ : ∀ x {xs ys} → xs ≼ ys → (x ∷ xs) ≼ (x ∷ ys)

  ≼⇒length-on-≤ : ∀ {xs ys} → xs ≼ ys → length xs ≤ length ys
  ≼⇒length-on-≤ []          = zero
  ≼⇒length-on-≤ (y ∺ xs≼ys) = ≤succ (≼⇒length-on-≤ xs≼ys)
  ≼⇒length-on-≤ (x ∷ xs≼ys) = succ (≼⇒length-on-≤ xs≼ys)
