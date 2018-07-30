module Base.Prop where

open import Base.Type
open import Base.Type.Equivalence
  hiding ( refl
         ; sym
         ; _∘_
         )
open import Base.Pi
open import Base.Sigma
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality

record Prop {ℓ} (A : Type ℓ) : Type ℓ where
  constructor intro
  field
    prop : (x y : A) → x ≡ y
open Prop ⦃...⦄
  public

instance
  Prop:≡ : ∀ {ℓ} {A : Type ℓ} {x y : A} → Prop (x ≡ y)
  Prop:≡ = Prop.intro uip

Symmetric-Prop-≅ :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    (_~_ : Relation ℓ₂ A) ⦃ _ : ∀ {x y} → Prop (x ~ y) ⦄ ⦃ _ : Symmetric _~_ ⦄
  → ∀ x y → (x ~ y) ≅ (y ~ x)
Symmetric-Prop-≅ _~_ x y = _≅_.intro sym sym (_⇄_.intro (λ _ → prop _ _) λ _ → prop _ _)

Σ≡-intro-prop :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    ⦃ _ : ∀ {x} → Prop (B x) ⦄
    (x y : Σ A B)
  → proj₁ x ≡ proj₁ y
  → x ≡ y
Σ≡-intro-prop _ _ γ = Σ≡-intro _ _ (γ , prop _ _)

to-prop-Σ-surj :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {P : B → Type ℓ₃}
    ⦃ _ : ∀ {x} → Prop (P x) ⦄
    {f : A → Σ B P}
  → SplitSurjective (proj₁ ∘ f)
  → SplitSurjective f
proj₁ (to-prop-Σ-surj ϕ (y , Py)) = proj₁ (ϕ y)
proj₂ (to-prop-Σ-surj ϕ (y , Py)) = Σ≡-intro-prop _ _ (proj₂ (ϕ y))
