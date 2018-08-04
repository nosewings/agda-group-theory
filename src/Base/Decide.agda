module Base.Decide where

open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi.Core
open import Base.Equality.Core
  hiding ( ind
         ; rec
         )

infix 5 _≟_

data Decide {ℓ} (A : Type ℓ) : Type ℓ where
  yes :   A → Decide A
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

-- Not sure what to call this. Decide is an exponential functor, with the
-- morphism mapping given below. By contrast, bind is "almost" a monadic bind,
-- except it also maps a morphism contravariantly.
bind : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (B → A) → (A → Decide B) → (Decide A → Decide B)
bind f k = rec k (no ∘ ¬.contramap f)

map : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → (B → A) → (Decide A → Decide B)
map f g = bind g (yes ∘ f)

decide : ∀ {ℓ} (A : Type ℓ) → ⦃ _ : Decide A ⦄ → Decide A
decide A = !!!

_≟_ : ∀ {ℓ} {A : Type ℓ} → ⦃ _ : ∀ {x y} → Decide (x ≡ y) ⦄ → (x y : A) → Decide (x ≡ y)
x ≟ y = decide (x ≡ y)
