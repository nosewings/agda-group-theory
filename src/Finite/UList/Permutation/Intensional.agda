module Finite.UList.Permutation.Intensional where

--------------------------------------------------------------------------------
-- An intensional representation of what it means for two ULists to be
-- permutations of each other.
--
-- This datatype is from van Laarhoven's "The complete correctness of sorting",
-- at https://twanvl.nl/blog/agda/sorting.
--------------------------------------------------------------------------------

open import Base.Type
open import Base.Relation
  hiding ( refl
         )
open import Base.Pi
open import Base.Equality
open import Base.Nat
  hiding ( refl
         )

open import Finite.UList
open import Finite.UList.Any

module _ {ℓ} {A : Type ℓ} where

  infix 4 _≈_

  data _▸_≡_ (a : A) : Relation ℓ (UList A) where
    here  : ∀ {xs a∉xs}             → a ▸ xs ≡ (a ∷ xs and a∉xs)
    there : ∀ {x xs x∉xs xas x∉xas} → a ▸ xs ≡ xas → a ▸ (x ∷ xs and x∉xs) ≡ (x ∷ xas and x∉xas)

  data _≈_ : Relation ℓ (UList A) where
    []  : [] ≈ []
    _∷_ : ∀ {a xs a∉xs ys yas} → a ▸ ys ≡ yas → xs ≈ ys → a ∷ xs and a∉xs ≈ yas

  ▸≡-delete : ∀ {a : A} {xs} (a∈xs : a ∈ xs) → a ▸ delete a∈xs ≡ xs
  ▸≡-delete (here  refl) = here
  ▸≡-delete (there a∈xs) = there (▸≡-delete a∈xs)

  abstract

    ▸≡-length : ∀ {a xs xas} → a ▸ xs ≡ xas → succ (length xs) ≡ length xas
    ▸≡-length here             = refl
    ▸≡-length (there a▸xs≡xas) = cong succ (▸≡-length a▸xs≡xas)

    ≈-preserves-length : ∀ {xs ys} → xs ≈ ys → length xs ≡ length ys
    ≈-preserves-length []                 = refl
    ≈-preserves-length (a▸ys≡yas ∷ xs≈ys) = cong succ (≈-preserves-length xs≈ys) ⟨ trans ⟩ ▸≡-length a▸ys≡yas
