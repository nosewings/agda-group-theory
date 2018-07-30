module Base.Type.Equivalence.Core where

open import Base.Level
open import Base.Type
open import Base.Pi
  as Π
  hiding ( id
         ; _⨾_
         ; _∘_
         )
open import Base.Equality
  hiding ( refl
         )
import Base.Relation
  as Relation

record _⇄_ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) (g : B → A) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor intro
  field
    unit : Π.id ≐ g Π.∘ f
    counit : f Π.∘ g ≐ Π.id

id : ∀ {ℓ} {A : Type ℓ} → (Π.id ∶ A ⟶ A) ⇄ (Π.id ∶ A ⟶ A)
id = intro (λ _ → _≡_.refl) (λ _ → _≡_.refl)

_⁻¹ :
  ∀ {ℓ₁} {ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {f : A → B} {g : B → A}
  → f ⇄ g
  → g ⇄ f
_⁻¹ (_⇄_.intro η ε) = _⇄_.intro (Relation.sym ε) (Relation.sym η)

-- Profunctorial composition.
_⨾_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    {f₁ : A → B} {g₁ : B → A}
    {f₂ : B → C} {g₂ : C → B}
  → f₁ ⇄ g₁
  → f₂ ⇄ g₂
  → (f₁ Π.⨾ f₂) ⇄ (g₂ Π.⨾ g₁)
_⨾_ {f₁ = f₁} {g₁} {f₂} {g₂} (_⇄_.intro η₁ ε₁) (_⇄_.intro η₂ ε₂) =
    _⇄_.intro (λ x → Relation.trans (η₁ x) (cong g₁ (η₂ (f₁ x))))
              (λ y → Relation.trans (cong f₂ (ε₁ (g₂ y))) (ε₂ y))

_∘_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    {f₁ : A → B} {g₁ : B → A}
    {f₂ : B → C} {g₂ : C → B}
  → f₂ ⇄ g₂
  → f₁ ⇄ g₁
  → (f₂ Π.∘ f₁) ⇄ (g₁ Π.∘ g₂)
_∘_ = flip _⨾_

record _≅_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor intro
  field
    to : A → B
    from : B → A
    to⇄from : to ⇄ from
  open _⇄_ to⇄from public

refl : ∀ {ℓ} {A : Type ℓ} → A ≅ A
refl = _≅_.intro Π.id Π.id id

sym :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
  → A ≅ B
  → B ≅ A
sym (_≅_.intro f g f⇄g) = _≅_.intro g f (f⇄g ⁻¹)

trans :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → A ≅ B → B ≅ C → A ≅ C
trans (_≅_.intro f₁ g₁ f₁⇄g₁) (_≅_.intro f₂ g₂ f₂⇄g₂) =
    _≅_.intro (f₂ Π.∘ f₁) (g₁ Π.∘ g₂) (f₁⇄g₁ ⨾ f₂⇄g₂)
