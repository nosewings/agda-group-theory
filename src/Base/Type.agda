module Base.Type where

open import Base.Level
  as Level

Type : ∀ ℓ → Set (Level.succ ℓ)
Type ℓ = Set ℓ
