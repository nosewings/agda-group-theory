module Base.Pi where

open import Base.Level
open import Base.Type
open import Base.Sigma.Core
open import Base.Relation
open import Base.Equality
  hiding ( refl
         )

open import Base.Pi.Core
  public

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂} where

  infix 4 _≐_

  _≐_ : Relation (ℓ₁ ⊔ ℓ₂) (Π A B)
  f ≐ g = ∀ x → f x ≡ g x

  instance

    Reflexive:≐ : Reflexive _≐_
    Reflexive:≐ = Reflexive.intro (λ _ → refl)

    Symmetric:≐ : Symmetric _≐_
    Symmetric:≐ = Symmetric.intro (λ Γ → λ x → sym (Γ x))

    Transitive:≐ : Transitive _≐_
    Transitive:≐ = Transitive.intro (λ Γ Ε → λ x → trans (Γ x) (Ε x))

Injective : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → Type (ℓ₁ ⊔ ℓ₂)
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

∘-preserves-injectivity :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    {g : B → C} → Injective g
  → {f : A → B} → Injective f
  → Injective (g ∘ f)
∘-preserves-injectivity ψ ϕ = λ g[f[x]]≡g[f[y]] → ϕ (ψ g[f[x]]≡g[f[y]])

SplitSurjective : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → Type (ℓ₁ ⊔ ℓ₂)
SplitSurjective f = Π[ y ] Σ[ x ] (f x ≡ y)

≐-preserves-surjectivity :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {f g : A → B}
  → f ≐ g
  → SplitSurjective f
  → SplitSurjective g
≐-preserves-surjectivity f≐g ϕ = λ b → proj₁ (ϕ b) , (sym f≐g (proj₁ (ϕ b)) ⟨ trans ⟩ proj₂ (ϕ b))

surj-∘-elim :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    (g : B → C) (f : A → B)
  → SplitSurjective (g ∘ f)
  → SplitSurjective g
proj₁ (surj-∘-elim g f ϕ c) = f (proj₁ (ϕ c))
proj₂ (surj-∘-elim g f ϕ c) = proj₂ (ϕ c)
