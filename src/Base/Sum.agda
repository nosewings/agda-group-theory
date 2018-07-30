module Base.Sum where

open import Base.Type
open import Base.Type.Negation
open import Base.Level
open import Base.Pi

infixr 1 _⊎_

data _⊎_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  inₗ : A → A ⊎ B
  inᵣ : B → A ⊎ B

ind :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂}
    (P : A ⊎ B → Type ℓ₃)
  → ((x : A) → P (inₗ x))
  → ((y : B) → P (inᵣ y))
  → Π (A ⊎ B) P
ind P l r (inₗ x) = l x
ind P l r (inᵣ y) = r y

rec :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {P : Type ℓ₃}
  → (A → P)
  → (B → P)
  → (A ⊎ B → P)
rec = ind _

bimap :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
  → (A → C)
  → (B → D)
  → A ⊎ B
  → C ⊎ D
bimap f g (inₗ a) = inₗ (f a)
bimap f g (inᵣ b) = inᵣ (g b)

lmap :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → (A → C)
  → A ⊎ B
  → C ⊎ B
lmap f = bimap f id

rmap :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {D : Type ℓ₃}
  → (B → D)
  → A ⊎ B
  → A ⊎ D
rmap g = bimap id g

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} where

  left : A ⊎ B → ¬ B → A
  left (inₗ a) ϕ = a
  left (inᵣ b) ϕ = b ↯ ϕ

  right : A ⊎ B → ¬ A → B
  right (inₗ a) ϕ = a ↯ ϕ
  right (inᵣ b) ϕ = b
