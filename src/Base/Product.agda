module Base.Product where

open import Base.Level
open import Base.Type
open import Base.Pi
open import Base.Sigma
  as Σ
  hiding ( ind
         ; rec
         )
open import Base.Equality
  hiding ( ind
         ; rec
         )

infixr 2 _×_

open import Base.Sigma
  public
  using ( _,_
        ; proj₁
        ; proj₂
        )

_×_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ₁ ⊔ ℓ₂)
A × B = Σ A (const B)

ind :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂}
    (P : A × B → Type ℓ₃)
  → ((x : A) (y : B) → P (x , y))
  → Π (A × B) P
ind = Σ.ind

rec :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {P : Type ℓ₃}
  → (A → B → P)
  → (A × B → P)
rec = ind _

×≡-intro :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    (u v : A × B)
  → (proj₁ u ≡ proj₁ v) × (proj₂ u ≡ proj₂ v)
  → u ≡ v
×≡-intro _ _ (refl , refl) = refl

×≡-elim :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    (u v : A × B)
  → u ≡ v
  → (proj₁ u ≡ proj₁ v × proj₂ u ≡ proj₂ v)
×≡-elim _ _ refl = refl , refl

map :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
  → (A → C) → (B → D) → A × B → C × D
map f g (a , b) = f a , g b
