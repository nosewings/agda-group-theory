module Base.Pi.Operation where

open import Base.Type
open import Base.Equality
open import Base.Nat.Core

module _ {ℓ} where

  Op : ℕ → Type ℓ → Type ℓ
  Op zero     A = A
  Op (succ n) A = A → Op n A

  Op₀ : Type ℓ → Type ℓ
  Op₀ = Op 0

  Op₁ : Type ℓ → Type ℓ
  Op₁ = Op 1

  Op₂ : Type ℓ → Type ℓ
  Op₂ = Op 2

  module _ {A : Type ℓ} (_∙_ : Op₂ A) where

    Associative : Type ℓ
    Associative = ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

    LeftCancellative : Type ℓ
    LeftCancellative = ∀ {y₁ y₂} x → x ∙ y₁ ≡ x ∙ y₂ → y₁ ≡ y₂

    RightCancellative : Type ℓ
    RightCancellative = ∀ {x₁ x₂} y → x₁ ∙ y ≡ x₂ ∙ y → x₁ ≡ x₂

    Commutative : Type ℓ
    Commutative = ∀ x y → x ∙ y ≡ y ∙ x

    module _ (ε : Op₀ A) where

      LeftIdentity : Type ℓ
      LeftIdentity = ∀ x → ε ∙ x ≡ x

      RightIdentity : Type ℓ
      RightIdentity = ∀ x → x ∙ ε ≡ x

      Idempotent : Type ℓ
      Idempotent = ε ∙ ε ≡ ε

      Involutive : Type ℓ
      Involutive = ∀ x → x ∙ x ≡ ε

      module _ (_⁻¹ : Op₁ A) where

        LeftInverse : Type ℓ
        LeftInverse = ∀ x → (x ⁻¹) ∙ x ≡ ε

        RightInverse : Type ℓ
        RightInverse = ∀ x → x ∙ (x ⁻¹) ≡ ε
