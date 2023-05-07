module Base.IsProp where

open import Base.Type
open import Base.Type.LogicalEquivalence
  hiding ( refl
         ; sym
         )
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

record IsProp {ℓ} (A : Type ℓ) : Type ℓ where
  constructor intro
  field
    prop : (x y : A) → x ≡ y
open IsProp ⦃...⦄
  public

instance
  IsProp:≡ : ∀ {ℓ} {A : Type ℓ} {x y : A} → IsProp (x ≡ y)
  IsProp:≡ = intro uip

Symmetric-IsProp-≅ :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    (_~_ : Relation ℓ₂ A) ⦃ _ : ∀ {x y} → IsProp (x ~ y) ⦄ ⦃ _ : Symmetric _~_ ⦄
  → ∀ x y → (x ~ y) ≅ (y ~ x)
Symmetric-IsProp-≅ _~_ x y = intro (intro sym sym) (intro (λ _ → prop _ _) λ _ → prop _ _)

Σ≡-intro-prop :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    ⦃ _ : ∀ {x} → IsProp (B x) ⦄
    (x y : Σ A B)
  → proj₁ x ≡ proj₁ y
  → x ≡ y
Σ≡-intro-prop _ _ γ = Σ≡-intro _ _ (γ , prop _ _)

to-prop-Σ-surj :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {P : B → Type ℓ₃}
    ⦃ _ : ∀ {x} → IsProp (P x) ⦄
    {f : A → Σ B P}
  → SplitSurjective (proj₁ ∘ f)
  → SplitSurjective f
proj₁ (to-prop-Σ-surj ϕ (y , Py)) = proj₁ (ϕ y)
proj₂ (to-prop-Σ-surj ϕ (y , Py)) = Σ≡-intro-prop _ _ (proj₂ (ϕ y))
