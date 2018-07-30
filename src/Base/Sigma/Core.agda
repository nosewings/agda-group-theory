module Base.Sigma.Core where

infix 3 Σ-syntax Σ-syntax′

open import Base.Level
open import Base.Type
open import Base.Pi.Core
open import Base.Equality
  hiding ( ind
         ; rec
         )

open import Agda.Builtin.Sigma
  public
  renaming ( fst to proj₁
           ; snd to proj₂
           )

ind :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    (P : Σ A B → Type ℓ₃)
  → ((x : A) (y : B x) → P (x , y))
  → Π (Σ A B) P
ind P p (x , y) = p x y

rec :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    {P : Type ℓ₃}
  → ((x : A) → B x → P)
  → (Σ A B → P)
rec = ind _

Σ-syntax : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
Σ-syntax = Σ
syntax Σ-syntax A (λ x → B) = Σ[ x ∶ A ] B

Σ-syntax′ : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} → (A → Type ℓ₂) → Type (ℓ₁ ⊔ ℓ₂)
Σ-syntax′ = Σ _
syntax Σ-syntax′ (λ x → B) = Σ[ x ] B

Σ≡-intro :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    (u v : Σ A B)
  → Σ[ γ ∶ proj₁ u ≡ proj₁ v ] (subst B γ (proj₂ u) ≡ proj₂ v)
  → u ≡ v
Σ≡-intro _ _ (refl , refl) = refl

Σ≡-elim :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    (u v : Σ A B)
  → u ≡ v
  → Σ[ γ ∶ proj₁ u ≡ proj₁ v ] (subst B γ (proj₂ u) ≡ proj₂ v)
Σ≡-elim _ _ refl = refl , refl

Σ≡-const-intro : 
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    (a : A)
    {b₁ b₂ : B a}
  → b₁ ≡ b₂
  → ((a , b₁) ∶ Σ A B) ≡ ((a , b₂) ∶ Σ A B)
Σ≡-const-intro a refl = refl
