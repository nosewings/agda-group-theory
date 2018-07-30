module Base.WellFounded.Acc where

open import Base.Level
open import Base.Type
open import Base.Pi
open import Base.Relation

data Acc {ℓ₁ ℓ₂} {A : Type ℓ₁} (_≺_ : Relation ℓ₂ A) (a : A) : Type (ℓ₁ ⊔ ℓ₂) where
  acc : ((x : A) → x ≺ a → Acc _≺_ x) → Acc _≺_ a

ind :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {_≺_ : Relation ℓ₂ A} {a : A}
    (P : Acc _≺_ a → Type ℓ₃)
  → ((ϕ : (x : A) → x ≺ a → Acc _≺_ x) → P (acc ϕ))
  → Π (Acc _≺_ a) P
ind P p (acc ϕ) = p ϕ

rec :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {_≺_ : Relation ℓ₂ A} {a : A}
    {P : Type ℓ₃}
  → (((x : A) → x ≺ a → Acc _≺_ x) → P)
  → (Acc _≺_ a → P)
rec = ind _

fold :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {_≺_ : Relation ℓ₂ A}
    (P : A → Type ℓ₃)
  → ((a : A) → ((x : A) → x ≺ a → P x) → P a)
  → (a : A) → Acc _≺_ a → P a
fold P f a (acc ϕ) = f a (λ x x≺a → fold P f x (ϕ x x≺a))

on-acc : 
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {_≺_ : Relation ℓ₃ B}
    (f : A → B)
    {a : A}
  → Acc _≺_ (f a) → Acc (_≺_ on f) a
on-acc f (acc ϕ) = acc (λ x fx≺fa → on-acc f (ϕ (f x) fx≺fa))
