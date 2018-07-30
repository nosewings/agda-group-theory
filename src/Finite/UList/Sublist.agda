module Finite.UList.Sublist where

open import Base.Level
  hiding ( zero
         ; succ
         )
open import Base.Type
open import Base.Relation
  hiding ( refl
         )
open import Base.Nat

open import Finite.UList.Core

module _ {ℓ} {A : Type ℓ} where

  infix 4 _≼_

  data _≼_ : Relation ℓ (UList A) where
    [] : [] ≼ []
    _∺_ : ∀ x {xs ys      x∉ys} → xs ≼ ys →                xs ≼ (x ∷ ys and x∉ys)
    _∷_ : ∀ x {xs ys x∉xs x∉ys} → xs ≼ ys → (x ∷ xs and x∉xs) ≼ (x ∷ ys and x∉ys)

  instance

    Reflexive:≼ : Reflexive _≼_
    Reflexive:≼ = Reflexive.intro aux where
      aux : ∀ {xs} → xs ≼ xs
      aux {[]}              = []
      aux {x ∷ xs and x∉xs} = x ∷ aux

    Transitive:≼ : Transitive _≼_
    Transitive:≼ = Transitive.intro aux where
      aux : ∀ {xs ys zs} → xs ≼ ys → ys ≼ zs → xs ≼ zs
      aux xs≼ys       []          = xs≼ys
      aux xs≼ys       (x ∺ ys≼zs) = x ∺ aux xs≼ys ys≼zs
      aux (x ∺ xs≼ys) (x ∷ ys≼zs) = x ∺ aux xs≼ys ys≼zs
      aux (x ∷ xs≼ys) (x ∷ ys≼zs) = x ∷ aux xs≼ys ys≼zs

  ≼⇒length≤′ : ∀ {xs ys} → xs ≼ ys → length xs ≤′ length ys
  ≼⇒length≤′ []          = refl
  ≼⇒length≤′ (x ∺ xs≼ys) = succ (≼⇒length≤′ xs≼ys)
  ≼⇒length≤′ (x ∷ xs≼ys) = succ≤′succ (≼⇒length≤′ xs≼ys)

-- ≼ preserves All and Any.
--
-- Of course, this happens in opposite directions. Moving from an overlist to a
-- sublist preserves All, and moving from a sublist to an overlist preserves Any.

≼-preserves-All : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} {xs ys : UList A} → xs ≼ ys → All P ys → All P xs
≼-preserves-All []          []         = []
≼-preserves-All (x ∺ xs≼ys) (Px ∷ Pxs) = ≼-preserves-All xs≼ys Pxs
≼-preserves-All (x ∷ xs≼ys) (Px ∷ Pxs) = Px ∷ ≼-preserves-All xs≼ys Pxs

≼-preserves-Any : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} {xs ys : UList A} → xs ≼ ys → Any P xs → Any P ys
≼-preserves-Any (x ∷ xs≼ys) (here Px)   = here Px
≼-preserves-Any (x ∷ xs≼ys) (there Pxs) = there (≼-preserves-Any xs≼ys Pxs)
≼-preserves-Any (x ∺ xs≼ys) Pxs         = there (≼-preserves-Any xs≼ys Pxs)

-- Specialized variants which are used frequently enough to deserve more helpful
-- names.

≼-preserves-∉ : ∀ {ℓ} {A : Type ℓ} {a : A} {xs ys : UList A} → xs ≼ ys → a ∉ ys → a ∉ xs
≼-preserves-∉ = ≼-preserves-All

≼-preserves-∈ : ∀ {ℓ} {A : Type ℓ} {a : A} {xs ys : UList A} → xs ≼ ys → a ∈ xs → a ∈ ys
≼-preserves-∈ = ≼-preserves-Any

difference : ∀ {ℓ} {A : Type ℓ} (xs ys : UList A) → xs ≼ ys → UList A
difference-∉ : ∀ {ℓ} {A : Type ℓ} (xs ys : UList A) (xs≼ys : xs ≼ ys) {a : A} → a ∉ ys → a ∉ difference xs ys xs≼ys

difference .[]            .[]               []          = []
difference xs             (y ∷ ys and a∉ys) (y ∺ xs≼ys) = y ∷ difference xs ys xs≼ys and difference-∉ xs ys xs≼ys a∉ys
difference (a ∷ xs and _) (a ∷ ys and _   ) (x ∷ xs≼ys) = difference xs ys xs≼ys

difference-∉ .[]            .[]            []          a∉ys         = []
difference-∉ xs             (y ∷ ys and _) (y ∺ xs≼ys) (y≢a ∷ a∉ys) = y≢a ∷ difference-∉ xs ys xs≼ys a∉ys
difference-∉ (_ ∷ xs and _) (_ ∷ ys and _) (_ ∷ xs≼ys) (_   ∷ a∉ys) = difference-∉ xs ys xs≼ys a∉ys
