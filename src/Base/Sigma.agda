module Base.Sigma where

open import Base.Type
open import Base.Type.LogicalEquivalence
open import Base.Type.Equivalence.Core
  hiding ( id
         ; _∘_
         )
open import Base.Pi
open import Base.Equality

open import Base.Sigma.Core
  public

Σ-assoc :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂} {C : (a : A) → B a → Type ℓ₃}
  → (Σ[ a ∶ A ] Σ[ b ∶ B a ] C a b) ≅ (Σ[ u ∶ Σ A B ] C (proj₁ u) (proj₂ u))
Σ-assoc = _≅_.intro (_↔_.intro (λ{ (a , b , c) → (a , b) , c }) λ{ ((a , b) , c) → a , b , c })
                    (_⇄_.intro (λ _ → _≡_.refl) (λ _ → _≡_.refl))

Σ-proj₂-≅-intro :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁}
    {B : A → Type ℓ₂}
    {C : A → Type ℓ₃}
  → (∀ x → B x ≅ C x)
  → Σ A B ≅ Σ A C
Σ-proj₂-≅-intro {A = A} {B} {C} ϕ = _≅_.intro (_↔_.intro f g) (_⇄_.intro η ε) where

  f : Σ A B → Σ A C
  f (a , b) = a , _≅_.to (ϕ a) b

  g : Σ A C → Σ A B
  g (a , c) = a , _≅_.from (ϕ a) c

  abstract

    η : id ≐ g ∘ f
    η (a , b) = Σ≡-const-intro a (_≅_.unit (ϕ a) b)

    ε : f ∘ g ≐ id
    ε (a , c) = Σ≡-const-intro a (_≅_.counit (ϕ a) c)
