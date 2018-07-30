module Base.Bool where

open import Base.Type
open import Base.Pi
open import Base.Equality
  hiding ( ind
         ; rec
         )
open import Base.Decide
  hiding ( ind
         ; rec
         )

infix 0 if_then_else_

open import Agda.Builtin.Bool
  public
  renaming ( Bool  to 𝟚
           ; false to 0₂
           ; true  to 1₂
           )

ind :
  ∀ {ℓ}
    (P : 𝟚 → Type ℓ)
  → P 0₂
  → P 1₂
  → Π 𝟚 P
ind P f t 0₂ = f
ind P f t 1₂ = t

rec : ∀ {ℓ} {P : Type ℓ} → P → P → 𝟚 → P
rec = ind _

if_then_else_ : ∀ {ℓ} {A : Type ℓ} → 𝟚 → A → A → A
if b then t else f = rec f t b

instance
  DecEq:Bool : ∀ {x y : 𝟚} → Decide (x ≡ y)
  DecEq:Bool {0₂} {0₂} = yes refl
  DecEq:Bool {0₂} {1₂} = no (λ ())
  DecEq:Bool {1₂} {0₂} = no (λ ())
  DecEq:Bool {1₂} {1₂} = yes refl
