module Base.Empty where

open import Base.Type
open import Base.Pi.Core
open import Base.FromNat

data 𝟘 : Type 0 where

ind :
  ∀ {ℓ}
    (P : 𝟘 → Type ℓ)
  → Π 𝟘 P
ind P ()

rec :
  ∀ {ℓ}
    {P : Type ℓ}
  → (𝟘 → P)
rec = ind _
