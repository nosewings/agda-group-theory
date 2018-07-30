module Base.Unit where

open import Base.Unit.Core
  public
open import Base.Equality
open import Base.Decide

instance
  DecEq:𝟙 : ∀ {x y : 𝟙} → Decide (x ≡ y)
  DecEq:𝟙 = yes refl
