module Finite.Equivalence where

open import Base.Type
open import Base.Type.Equivalence
open import Base.Nat
open import Base.Fin

record Size {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  constructor intro
  field
    equivalence : A ≅ Fin n
open Size ⦃...⦄
  public

record Finite {ℓ} (A : Type ℓ) : Type ℓ where
  constructor intro
  field
    size : ℕ
    ⦃ has-size ⦄ : Size A size
open Finite ⦃...⦄
  public
