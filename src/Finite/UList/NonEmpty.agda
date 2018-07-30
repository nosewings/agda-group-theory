module Finite.UList.NonEmpty where

open import Base.Level
open import Base.Type
open import Base.Pi
open import Base.Maybe
  hiding ( Any
         )
open import Base.Equality
open import Base.Nat
  as ℕ
  using ( ℕ
        )

infix 4 _∈_

open import Finite.UList
  as UL
  using ( UList
        ; []
        ; _∷_and_
        ; _∉_
        )
import Finite.UList.All
  as UL∀
import Finite.UList.Any
  as UL∃

record UList⁺ {ℓ} (A : Type ℓ) : Type ℓ where
  constructor _∷_and_
  field
    head : A
    tail : UList A
    head∉tail : head UL.∉ tail
open UList⁺ public

from-UList : ∀ {ℓ} {A : Type ℓ} → UList A → Maybe (UList⁺ A)
from-UList []                = none
from-UList (x ∷ xs and x∉xs) = just (x ∷ xs and x∉xs)

to-UList : ∀ {ℓ} {A : Type ℓ} → UList⁺ A → UList A
to-UList (x ∷ xs and x∉xs) = x ∷ xs and x∉xs

All : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → Type ℓ₂) → UList⁺ A → Type (ℓ₁ ⊔ ℓ₂)
All P = UL∀.All P ∘ to-UList

Any : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → Type ℓ₂) → UList⁺ A → Type (ℓ₁ ⊔ ℓ₂)
Any P = UL∃.Any P ∘ to-UList

_∈_ : ∀ {ℓ} {A : Type ℓ} → A → UList⁺ A → Type ℓ
x ∈ xs = Any (_≡ x) xs

fold :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
  → (A → B → B) → B → UList⁺ A → B
fold _·_ e = UL.fold _·_ e ∘ to-UList 

length : ∀ {ℓ} {A : Type ℓ} → UList⁺ A → ℕ
length = UL.length ∘ to-UList
