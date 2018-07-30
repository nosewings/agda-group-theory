module Base.Unit.Core where

open import Base.Type
open import Base.Pi.Core

open import Agda.Builtin.Unit
  public
  using (
        )
  renaming ( ⊤ to 𝟙
           )

ind :
  ∀ {ℓ}
    (P : 𝟙 → Type ℓ)
  → P _
  → Π 𝟙 P
ind P z _ = z

rec :
  ∀ {ℓ}
    {P : Type ℓ}
  → P
  → (𝟙 → P)
rec = ind _
