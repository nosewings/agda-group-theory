module Base.Unit.Core where

open import Base.Type
open import Base.Pi.Core

open import Agda.Builtin.Unit
  public
  renaming ( ⊤ to 𝟙
           ; tt to 0₁
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
