module Finite.UList.Image where

open import Base.Type
open import Base.Level
open import Base.Pi
open import Base.Sigma
open import Base.Product
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality
  as ≡
open import Base.Prop

open import Finite.UList
  as UList
open import Finite.UList.Any
  as UListAny

Image : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → Type (ℓ₁ ⊔ ℓ₂)
Image f = Σ[ y ] Σ[ x ] f x ≡ y

Image≡-intro :
    ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂}
      (f : A → B)
      (u v : Image f)
    → let (y₁ , x₁ , γ) = u
          (y₂ , x₂ , η) = v
      in (y₁ ≡ y₂ × x₁ ≡ x₂) → u ≡ v
Image≡-intro f (_ , _ , refl) (_ , _ , refl) (refl , refl) = refl

private

  module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} where

    to-Image : (f : A → B) → A → Image f
    to-Image f x = f x , x , refl

    to-Image-stable : {f : A → B} {y : B} {x : A} (f[x]≡y : f x ≡ y) → (y , x , f[x]≡y) ≡ to-Image f x
    to-Image-stable {f} {y} {x} = ≡.ind (λ b γ → (b , x , γ) ≡ to-Image f x) refl y

module _
    {ℓ₁ ℓ₂}
    {A : Type ℓ₁} ⦃ _ : Finite A ⦄
    {B : Type ℓ₂}
    (f : A → B) (inj : Injective f)
    where

  private

    Image-elements : UList (Image f)
    Image-elements = UList.map (to-Image f) (λ{ refl → refl }) (elements-of A)

  instance

    Enumeration:InjectiveImage : Enumeration Image-elements
    Enumeration:InjectiveImage = Enumeration.intro aux where
      aux : (β : Image f) → β UListAny.∈ Image-elements
      aux (y , x , f[x]≡y) = subst (UListAny._∈ Image-elements) (sym {_~_ = _≡_} (to-Image-stable f[x]≡y)) (∈-map _ _ (locate x))

    Finite:InjectiveImage : Finite (Image f)
    Finite:InjectiveImage = Finite.intro Image-elements

  Image-size : size-of (Image f) ≡ size-of A
  Image-size = UList.map-length (to-Image f) _ (elements-of A)
