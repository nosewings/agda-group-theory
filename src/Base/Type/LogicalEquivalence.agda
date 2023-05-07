module Base.Type.LogicalEquivalence where

open import Base.Level
open import Base.Type
open import Base.Pi

infix 4 _↔_

record _↔_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor intro
  field
    to   : A → B
    from : B → A

refl : ∀ {ℓ} {A : Type ℓ} → A ↔ A
refl = intro id id

sym : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A ↔ B → B ↔ A
sym (intro f g) = intro g f

trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} → A ↔ B → B ↔ C → A ↔ C
trans (intro f₁ g₁) (intro f₂ g₂) = intro (f₂ ∘ f₁) (g₁ ∘ g₂)
