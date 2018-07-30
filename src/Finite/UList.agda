module Finite.UList where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality
open import Base.Decide
  as Decide
open import Base.Nat

open import Finite.UList.Core
open import Finite.UList.All
open import Finite.UList.Any

open import Finite.UList.Core
  public
  hiding ( All
         ; Any
         )

record Enumeration {ℓ} {A : Type ℓ} (xs : UList A) : Type ℓ where
  constructor intro
  field
    locate : ∀ x → x ∈ xs
open Enumeration ⦃...⦄
  public

locate-in : ∀ {ℓ} {A : Type ℓ} (xs : UList A) ⦃ _ : Enumeration xs ⦄ (x : A) → x ∈ xs
locate-in _ = Enumeration.locate !

record Finite {ℓ} (A : Type ℓ) : Type ℓ where
  constructor intro
  field
    elements : UList A
    ⦃ enumeration ⦄ : Enumeration elements
open Finite ⦃...⦄
  public

elements-of : ∀ {ℓ} (A : Type ℓ) → ⦃ _ : Finite A ⦄ → UList A
elements-of A = Finite.elements !

size-of : ∀ {ℓ} (A : Type ℓ) → ⦃ _ : Finite A ⦄ → ℕ
size-of A ⦃ ϕ ⦄ = length (elements-of A)

private
  Decide≡-based-on :
    ∀ {ℓ}
      {A : Type ℓ}
      {as : UList A}
      {x y}
    → x ∈ as → y ∈ as → Decide (x ≡ y)
  Decide≡-based-on                       (here  refl) (here  refl) = yes refl
  Decide≡-based-on {as = _ ∷ _ and x∉as} (here  refl) (there y∈as) = no (sym (apply x∉as y∈as))
  Decide≡-based-on {as = _ ∷ _ and y∉as} (there x∈as) (here  refl) = no (apply y∉as x∈as)
  Decide≡-based-on                       (there x∈as) (there y∈as) = Decide≡-based-on x∈as y∈as

instance

  Finite⇒Decide:≡ :
    ∀ {ℓ}
      {A : Type ℓ} ⦃ _ : Finite A ⦄
      {x y : A}
    → Decide (x ≡ y)
  Finite⇒Decide:≡ {A = A} {x = x} {y} = Decide≡-based-on (locate-in (elements-of A) x) (locate-in (elements-of A) y)

  Finite⇒Decide:Σ :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁} ⦃ _ : Finite A ⦄
      {P : A → Type ℓ₂} ⦃ _ : ∀ {x} → Decide (P x) ⦄
    → Decide (Σ A P)
  Finite⇒Decide:Σ {A = A} {P} = Decide.map aux₁ aux₂ (decide (Any P (elements-of A))) where

    aux₁ : Any P (elements-of A) → Σ A P
    aux₁ ∃enumerationP = let (x , _ , Px) = extract ∃enumerationP
                         in x , Px

    aux₂ : Σ A P → Any P (elements-of A)
    aux₂ (x , Px) = compress (x , locate x , Px)
