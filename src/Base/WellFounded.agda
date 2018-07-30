module Base.WellFounded where

open import Base.Level
open import Base.Type
open import Base.Pi
open import Base.Relation
open import Base.WellFounded.Acc

open import Base.WellFounded.Acc
  public
  using ( Acc
        ; acc
        )

WellFounded : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → Relation ℓ₂ A → Type (ℓ₁ ⊔ ℓ₂)
WellFounded _≺_ = ∀ x → Acc _≺_ x

induction :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {_≺_ : Relation ℓ₂ A}
  → WellFounded _≺_
  → (P : A → Type ℓ₃)
  → ((a : A) → ((x : A) → x ≺ a → P x) → P a)
  → Π A P
induction wf P ϕ x = Base.WellFounded.Acc.fold P ϕ x (wf x)

recursion :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {_≺_ : Relation ℓ₂ A}
  → WellFounded _≺_
  → {P : Type ℓ₃}
  → ((a : A) → ((x : A) → x ≺ a → P) → P)
  → (A → P)
recursion wf = induction wf _

on-wf :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {_≺_ : Relation ℓ₃ B}
    (f : A → B)
  → WellFounded _≺_
  → WellFounded (_≺_ on f)
on-wf f wf = λ x → on-acc f (wf (f x))
