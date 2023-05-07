module Base.FromNat where

open import Base.Level
  as Level
open import Base.Type
open import Base.Pi.Core
open import Base.Unit.Core
open import Base.Nat.Core
  as ℕ

open import Agda.Builtin.FromNat
  public
  renaming ( Number to FromNat
           )

instance

  FromNat:Level : FromNat Level
  FromNat:Level = record
    { Constraint = const 𝟙
    ; fromNat    = ℕ.rec Level.zero (λ _ ℓ → Level.succ ℓ)
    }

  FromNat:ℕ : FromNat ℕ
  FromNat:ℕ = record
    { Constraint = const 𝟙
    ; fromNat    = λ n → n
    }
