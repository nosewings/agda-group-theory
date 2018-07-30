module Base.Type.Negation where

open import Base.Type
open import Base.Pi.Core
open import Base.Empty
  as 𝟘
open import Base.Type.Negation.Double
  as ¬¬

open import Base.Type.Negation.Core
  public
  using ( ¬_
        ; _⊥_
        )
  renaming ( contrapositive to contramap
           )

contradict : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → ¬ B) → (B → ¬ A)
contradict f = contramap f ∘ ¬¬.intro

_↯_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A → ¬ A → B
_↯_ x = 𝟘.rec ∘ ¬¬.intro x
