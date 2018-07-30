module Finite.UList.Permutation where

open import Base.Type
open import Base.Product
open import Base.Equality

open import Finite.UList
open import Finite.UList.Any

open import Finite.UList.Permutation.Extensional
  renaming ( _≈_ to _≈ᴱ_
           )
open import Finite.UList.Permutation.Intensional
  renaming ( _≈_ to _≈ᴵ_
           )

module _ {ℓ} {A : Type ℓ} where

  extensional⇒intensional : {xs ys : UList A} → xs ≈ᴱ ys → xs ≈ᴵ ys
  extensional⇒intensional {[]}              {ys}              []≈ᴱys rewrite []≈ []≈ᴱys = []
  extensional⇒intensional {xs}              {[]}              xs≈ᴱ[] rewrite ≈[] xs≈ᴱ[] = []  
  extensional⇒intensional {x ∷ xs and x∉xs} {y ∷ ys and y∉ys} xs≈ᴱys =
      lemma ∷ extensional⇒intensional (≈delete xs≈ᴱys) where

    ys′ : UList A
    ys′ = delete (proj₁ (xs≈ᴱys x) (here refl))

    lemma : x ▸ ys′ ≡ (y ∷ ys and y∉ys)
    lemma = ▸≡-delete (proj₁ (xs≈ᴱys x) (here refl))
