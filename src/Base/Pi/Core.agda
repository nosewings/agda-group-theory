module Base.Pi.Core where

open import Base.Level
open import Base.Type

infixr  9  _∘_
infix   3 Π-syntax Π-syntax′
infixl  1 _⟨_⟩_
infixl  1 _on_
infix   0 case_return_of_ case_of_
infixr  0 _⟶_ _$_
infix  -1 annotate

Π : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
Π A B = (x : A) → B x

Π-syntax : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
Π-syntax = Π
syntax Π-syntax A (λ x → B) = Π[ x ∶ A ] B

Π-syntax′ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
Π-syntax′ = Π _
syntax Π-syntax′ (λ x → B) = Π[ x ] B

_⟶_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
A ⟶ B = A → B

_$_ :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
  → Π A B → (x : A) → B x
f $ x = f x

id : ∀ {ℓ} {A : Type ℓ} → (A → A)
id = λ x → x

const : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A → (B → A)
const x = λ _ → x

_∘_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁}
    {B : A → Type ℓ₂}
    {C : (x : A) → B x → Type ℓ₃}
  → ({x : A} → Π (B x) (C x))
  → (f : Π A B)
  → ((x : A) → C x (f x))
g ∘ f = λ x → g (f x)

flip :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : A → B → Type ℓ₃}
  → ((x : A) (y : B) → C x y)
  → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

_⟨_⟩_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → A → (A → B → C) → B → C
x ⟨ f ⟩ y = f x y

_on_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → (B → B → C)
  → (A → B)
  → (A → A → C)
_·_ on f = λ x y → f x · f y

case_return_of_ :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} (x : A)
    (B : A → Type ℓ₂)
  → ((x : A) → B x)
  → B x
case x return B of f = f x

case_of_ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → A → (A → B) → B
case x of f = case x return _ of f

annotate : ∀ {ℓ} (A : Type ℓ) → A → A
annotate _ x = x
syntax annotate A x = x ∶ A

!!! : ∀ {ℓ} {A : Type ℓ} → ⦃ _ : A ⦄ → A
!!! ⦃ x ⦄ = x
