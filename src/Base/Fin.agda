module Base.Fin where

--------------------------------------------------------------------------------
-- Fin(n) is the canonical type with n elements.
--------------------------------------------------------------------------------

open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Decide
open import Base.Equality
open import Base.Nat
open import Base.FromNat

data Fin : ℕ → Type 0 where
  zero : ∀ {n} → Fin (succ n)
  succ : ∀ {n} → Fin n → Fin (succ n)

succ-inj : ∀ {n} → Injective (succ ∶ Fin n ⟶ Fin (succ n))
succ-inj refl = refl

zero≢succ : ∀ {n} (i : Fin n) → Fin.zero ≢ Fin.succ i
zero≢succ _ = λ ()

succ≢zero : ∀ {n} (i : Fin n) → Fin.succ i ≢ Fin.zero
succ≢zero _ = λ ()

instance
  DecEq:Fin : ∀ {n} {i j : Fin n} → Decide (i ≡ j)
  DecEq:Fin {i = zero}   {zero}   = yes refl
  DecEq:Fin {i = zero}   {succ j} = no (zero≢succ j)
  DecEq:Fin {i = succ i} {zero}   = no (succ≢zero i)
  DecEq:Fin {i = succ i} {succ j} with i ≟ j
  ... | yes i≡j = yes (cong succ i≡j)
  ... | no  i≢j = no  (¬.contramap succ-inj i≢j)
