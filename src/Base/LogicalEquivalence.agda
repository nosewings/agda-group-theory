module Base.LogicalEquivalence where

open import Base.Level
open import Base.Type
open import Base.Pi
open import Base.Product

infix 4 _↔_

_↔_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
A ↔ B = (A → B) × (B → A)

refl : ∀ {ℓ} {A : Type ℓ} → A ↔ A
refl = id , id

sym : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A ↔ B → B ↔ A
sym (f , g) = (g , f)

trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} → A ↔ B → B ↔ C → A ↔ C
trans (f₁ , g₁) (f₂ , g₂) = (f₂ ∘ f₁ , g₁ ∘ g₂)
