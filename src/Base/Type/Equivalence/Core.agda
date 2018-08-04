module Base.Type.Equivalence.Core where

open import Base.Level
open import Base.Type
open import Base.Type.LogicalEquivalence
  as LogicalEquivalence
  hiding ( refl
         ; sym
         ; trans
         )
open import Base.Pi
  as Π
  hiding ( id
         ; _∘_
         )
open import Base.Equality
  hiding ( refl
         )
import Base.Relation
  as Relation

infixr 9 _∘_

record _⇄_ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) (g : B → A) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor intro
  field
    unit   : Π.id ≐ g Π.∘ f
    counit : f Π.∘ g ≐ Π.id

id : ∀ {ℓ} {A : Type ℓ} → (Π.id ∶ A ⟶ A) ⇄ (Π.id ∶ A ⟶ A)
id = intro (λ _ → _≡_.refl) (λ _ → _≡_.refl)

_⁻¹ :
  ∀ {ℓ₁} {ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {f : A → B} {g : B → A}
  → f ⇄ g
  → g ⇄ f
(_⇄_.intro η ε) ⁻¹ = _⇄_.intro (Relation.sym ε) (Relation.sym η)

_∘_ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    {f₂ : B → C} {g₂ : C → B}
    {f₁ : A → B} {g₁ : B → A}
  → f₂ ⇄ g₂
  → f₁ ⇄ g₁
  → (f₂ Π.∘ f₁) ⇄ (g₁ Π.∘ g₂)
_∘_ {f₂ = f₂} {g₂} {f₁} {g₁} (_⇄_.intro η₂ ε₂) (_⇄_.intro η₁ ε₁) =
    _⇄_.intro (λ a → η₁ a                ⟨ Relation.trans ⟩ cong g₁ (η₂ (f₁ a)))
              (λ c → cong f₂ (ε₁ (g₂ c)) ⟨ Relation.trans ⟩ ε₂ c               )

record _≅_ {ℓ₁ ℓ₂} (A : Type ℓ₁) (B : Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor intro
  field
    to↔from : A ↔ B
  open _↔_ to↔from
    public
  field
    to⇄from : to ⇄ from
  open _⇄_ to⇄from
    public

refl : ∀ {ℓ} {A : Type ℓ} → A ≅ A
refl = _≅_.intro LogicalEquivalence.refl id

sym :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
  → A ≅ B
  → B ≅ A
sym (_≅_.intro f↔g f⇄g) = _≅_.intro (LogicalEquivalence.sym f↔g) (f⇄g ⁻¹)

trans :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
  → A ≅ B → B ≅ C → A ≅ C
trans (_≅_.intro f₁↔g₁ f₁⇄g₁) (_≅_.intro f₂↔g₂ f₂⇄g₂) =
    _≅_.intro (LogicalEquivalence.trans f₁↔g₁ f₂↔g₂)
              (f₂⇄g₂ ∘ f₁⇄g₁)
