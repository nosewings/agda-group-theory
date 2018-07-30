module Base.Nat.Core where

open import Base.Type
open import Base.Pi.Core

open import Agda.Builtin.Nat
  public
  using ( zero
        ; _+_
        ; _-_
        ; _*_
        )
  renaming ( Nat to ℕ
           ; suc to succ
           )

ind :
  ∀ {ℓ}
    (P : ℕ → Type ℓ)
  → P zero
  → ((x : ℕ) → P x → P (succ x))
  → Π ℕ P
ind P z s zero     = z
ind P z s (succ n) = s n (ind P z s n)

rec :
  ∀ {ℓ}
    {P : Type ℓ}
  → P
  → (ℕ → P → P)
  → (ℕ → P)
rec = ind _
