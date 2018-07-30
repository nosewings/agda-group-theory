module Base.Equality.Core where

open import Base.Type
open import Base.Pi.Core

open import Agda.Builtin.Equality
  public

ind :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {a : A}
    (P : (x : A) → a ≡ x → Type ℓ₂)
  → P a refl
  → (x : A) → Π (a ≡ x) (P x)
ind P r _ refl = r

rec :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {a : A}
    (P : A → Type ℓ₂)
  → P a
  → (x : A) → (a ≡ x → P x)
rec P = ind (const ∘ P)

uip : ∀ {ℓ} {A : Type ℓ} {x y : A} (η ε : x ≡ y) → η ≡ ε
uip refl refl = refl

axiom-k : ∀ {ℓ} {A : Type ℓ} {x : A} (η : x ≡ x) → η ≡ refl
axiom-k η = uip η refl
