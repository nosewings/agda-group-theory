module Examples where

open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality

open import Base.Unit
open import Finite.Types.Unit
open import Algebra.Group.Groups.Unit

open import Base.Bool
open import Finite.Types.Bool
open import Algebra.Group.Groups.Bool

open import Algebra.Group
open import Algebra.Group.Lagrange

instance

  -- The trivial homomorphism from 𝟙 to any group.
  𝟙-mono : ∀ {ℓ} {G : Type ℓ} ⦃ _ : Group G ⦄ → Monomorphism {G₁ = 𝟙} {G₂ = G} (const ε)
  𝟙-mono = record { homomorphism = record { homo-· = λ _ _ → sym (left-id ε) }
                  ; injective    = const refl
                  }

test : _
test = lagrange 𝟚 𝟙 (const ε)
