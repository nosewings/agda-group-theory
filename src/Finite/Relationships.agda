module Finite.Relationships where

open import Base.Type
open import Base.Type.Equivalence
  as ≅
  hiding ( id
         ; _∘_
         ; sym
         ; trans
         )
open import Base.Pi
open import Base.Sigma
open import Base.Relation
  hiding ( Equivalence
         )
open import Base.Equality
open import Base.Nat
open import Base.Fin

open import Finite.UList
  as UList
open import Finite.UList.Permutation
open import Finite.UVec
  as UVec
open import Finite.Equivalence
  as Equivalence

module _ {ℓ} {A : Type ℓ} where

UVecSize⇒EquivalenceSize :
  ∀ {ℓ n}
    {A : Type ℓ}
  → UVec.Size A n
  → Equivalence.Size A n
UVecSize⇒EquivalenceSize {n = n} {A} (UVec.Size.intro xs ⦃ ϕ ⦄) = Equivalence.Size.intro (_≅_.intro f g (_⇄_.intro η ε)) where
  f : A → Fin n
  f = proj₁ ∘ ∈⇒index ∘ UVec.Enumeration.locate ϕ
  g : Fin n → A
  g = UVec.index xs
  abstract
    η : id ≐ g ∘ f
    η = sym ∘ proj₂ ∘ ∈⇒index ∘ UVec.Enumeration.locate ϕ
    ε : f ∘ g ≐ id
    ε = index-inj _ ∘ sym ∘ η ∘ g

UVecFinite⇒EquivalenceFinite : ∀ {ℓ} {A : Type ℓ} → UVec.Finite A → Equivalence.Finite A
UVecFinite⇒EquivalenceFinite (UVec.Finite.intro n ⦃ ϕ ⦄) = Equivalence.Finite.intro n ⦃ UVecSize⇒EquivalenceSize ϕ ⦄

EquivalenceSize⇒UVecSize :
  ∀ {ℓ n}
    {A : Type ℓ}
  → Equivalence.Size A n
  → UVec.Size A n
EquivalenceSize⇒UVecSize {n = n} {A} (Equivalence.Size.intro ϕ@(_≅_.intro f g (_⇄_.intro η ε))) =
    UVec.Size.intro elems ⦃ Enumeration.intro lemma ⦄ where
  elems : UVec A n
  elems = UVec.map g (from-inj ϕ) (UVec.fins n)
  lemma : ∀ x → x UVec.∈ elems
  lemma x = subst (λ a → a UVec.∈ elems) (sym η x) (UVec.map-∈ g _ (UVec.fins-∈ (f x)))

EquivalenceFinite⇒UVecFinite : ∀ {ℓ} {A : Type ℓ} → Equivalence.Finite A → UVec.Finite A
EquivalenceFinite⇒UVecFinite (Equivalence.Finite.intro n ⦃ ϕ ⦄) = UVec.Finite.intro n ⦃ EquivalenceSize⇒UVecSize ϕ ⦄

UListFinite⇒UVecSize : ∀ {ℓ} {A : Type ℓ} (ϕ : UList.Finite A) → UVec.Size A (UList.length (UList.Finite.elements ϕ))
UListFinite⇒UVecSize (UList.Finite.intro xs ⦃ UList.Enumeration.intro f ⦄) =
    UVec.Size.intro (UVec.from-UList xs) ⦃ UVec.Enumeration.intro (λ x → UVec.from-UList-∈ (f x)) ⦄

UListFinite⇒UVecFinite : ∀ {ℓ} {A : Type ℓ} → UList.Finite A → UVec.Finite A
UListFinite⇒UVecFinite ϕ@(UList.Finite.intro xs) = UVec.Finite.intro (UList.length xs) ⦃ UListFinite⇒UVecSize ϕ ⦄

UVecFinite⇒UListFinite : ∀ {ℓ} {A : Type ℓ} → UVec.Finite A → UList.Finite A
UVecFinite⇒UListFinite (UVec.Finite.intro n ⦃ UVec.Size.intro xs ⦃ UVec.Enumeration.intro f ⦄ ⦄) =
    UList.Finite.intro (UVec.to-UList xs) ⦃ UList.Enumeration.intro λ x → to-UList-∈ (f x) ⦄

UListFinite⇒EquivalenceFinite : ∀ {ℓ} {A : Type ℓ} → UList.Finite A → Equivalence.Finite A
UListFinite⇒EquivalenceFinite = UVecFinite⇒EquivalenceFinite ∘ UListFinite⇒UVecFinite

EquivalenceFinite⇒UListFinite : ∀ {ℓ} {A : Type ℓ} → Equivalence.Finite A → UList.Finite A
EquivalenceFinite⇒UListFinite = UVecFinite⇒UListFinite ∘ EquivalenceFinite⇒UVecFinite

abstract
  UListEnumerations-≅-sizes :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁} {B : Type ℓ₂}
      (as : UList A) (ϕ : UList.Enumeration as)
      (bs : UList B) (ψ : UList.Enumeration bs)
    → A ≅ B
    → UList.length as ≡ UList.length bs
  UListEnumerations-≅-sizes {A = A} {B} as ϕ bs ψ A≅B =
      UList.length as
        ≡⟨⟩
      UVec.Finite.size uvfin-B
        ≡⟨ to-UList-length (UVec.Size.elements (UVec.Finite.has-size uvfin-B)) ⟩⁻¹
      UList.length bs′
        ≡⟨ ≈-preserves-length (enumerations-are-permutations bs′ ψ′ bs ψ) ⟩
      UList.length bs
        ∎ where

    open ≡Reasoning

    eqfin-A : Equivalence.Finite A
    eqfin-A = UListFinite⇒EquivalenceFinite (UList.Finite.intro as ⦃ ϕ ⦄)

    B≅Fin : B ≅ Fin (UList.length as)
    B≅Fin = ≅.sym A≅B ⟨ ≅.trans ⟩ Equivalence.Size.equivalence (Equivalence.Finite.has-size eqfin-A)

    eqfin-B : Equivalence.Finite B
    eqfin-B = Equivalence.Finite.intro (UList.length as) ⦃ Equivalence.Size.intro B≅Fin ⦄

    uvfin-B : UVec.Finite B
    uvfin-B = EquivalenceFinite⇒UVecFinite eqfin-B

    ulfin-B : UList.Finite B
    ulfin-B = EquivalenceFinite⇒UListFinite eqfin-B

    bs′ : UList B
    bs′ = UList.Finite.elements ulfin-B

    ψ′ : UList.Enumeration bs′
    ψ′ = UList.Finite.enumeration ulfin-B
