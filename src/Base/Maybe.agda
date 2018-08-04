module Base.Maybe where

open import Base.Level
open import Base.Type
open import Base.Pi

data Maybe {ℓ} (A : Type ℓ) : Type ℓ where
  none : Maybe A
  some : A → Maybe A

ind :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    (P : Maybe A → Type ℓ₂)
  → P none
  → (∀ x → P (some x))
  → Π (Maybe A) P
ind P n j none     = n
ind P n j (some x) = j x

rec :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    {P : Type ℓ₂}
  → P
  → (A → P)
  → (Maybe A → P)
rec = ind _

bind :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
  → (A → Maybe B)
  → (Maybe A → Maybe B)
bind f = rec none f

map :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
  → (A → B)
  → (Maybe A → Maybe B)
map f = bind (some ∘ f)

data All {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : Maybe A → Type (ℓ₁ ⊔ ℓ₂) where
  none :               All P none
  some : ∀ {x} → P x → All P (some x)

data Any {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : Maybe A → Type (ℓ₁ ⊔ ℓ₂) where
  here : ∀ {x} → P x → Any P (some x)
