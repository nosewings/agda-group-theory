module Base.Type.Negation.Core where

open import Base.Type
open import Base.Empty

infix 3 ¬_ ¬¬_

¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬ A = A → 𝟘

_⊥_ : ∀ {ℓ} {A : Type ℓ} → A → ¬ A → 𝟘
x ⊥ ϕ = ϕ x

¬¬_ : ∀ {ℓ} → Type ℓ → Type ℓ
¬¬ A = ¬ ¬ A

¬¬-intro : ∀ {ℓ} {A : Type ℓ} → A → ¬¬ A
¬¬-intro x = λ ϕ → x ⊥ ϕ

contrapositive : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → (¬ B → ¬ A)
contrapositive f = λ ϕ x → ¬¬-intro (f x) ϕ
