module Base.Decide where

open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi.Core
open import Base.Equality.Core
  hiding ( ind
         ; rec
         )

data Decide {ℓ} (A : Type ℓ) : Type ℓ where
  yes : A   → Decide A
  no  : ¬ A → Decide A

ind :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    (P : Decide A → Type ℓ₂)
  → (∀ x → P (yes x))
  → (∀ ϕ → P (no ϕ))
  → Π (Decide A) P
ind P y n (yes x) = y x
ind P y n (no  ϕ) = n ϕ

rec :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    {P : Type ℓ₂}
  → (A → P)
  → (¬ A → P)
  → (Decide A → P)
rec = ind _

bimap : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → (B → A) → Decide A → Decide B
bimap f g = rec (yes ∘ f) (no ∘ ¬.contramap g)

decide : ∀ {ℓ} (A : Type ℓ) → ⦃ _ : Decide A ⦄ → Decide A
decide A = !

_≟_ : ∀ {ℓ} {A : Type ℓ} → ⦃ _ : ∀ {x y} → Decide (x ≡ y) ⦄ → (x y : A) → Decide (x ≡ y)
x ≟ y = decide (x ≡ y)
