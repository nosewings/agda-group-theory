module Base.Type.Negation.Double where

open import Base.Type
open import Base.Pi.Core
open import Base.Type.Negation.Core

open import Base.Type.Negation.Core
  public
  using ( ¬¬_
        )
  renaming ( ¬¬-intro       to intro
           )

bind : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → ¬¬ B) → (¬¬ A → ¬¬ B)
bind f = contrapositive (contrapositive f ∘ intro)

map : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → (¬¬ A → ¬¬ B)
map f = bind (intro ∘ f)
