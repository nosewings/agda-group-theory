module Base.Equality where

open import Base.Level
open import Base.Type
open import Base.Type.Negation
open import Base.Pi.Core
open import Base.Empty
open import Base.Equality.Core
  as ≡
  public
open import Base.Relation
  hiding ( refl
         )

module _ {ℓ} {A : Type ℓ} where
  instance

    Reflexive:≡ : Reflexive (_≡_ ∶ Relation ℓ A)
    Reflexive:≡ = intro refl

    Symmetric:≡ : Symmetric (_≡_ ∶ Relation ℓ A)
    Symmetric:≡ = intro λ{ refl → refl }

    Transitive:≡ : Transitive (_≡_ ∶ Relation ℓ A)
    Transitive:≡ = intro λ{ refl refl → refl }

    Preorder:≡ : Preorder (_≡_ ∶ Relation ℓ A)
    Preorder:≡ = intro

    Equivalence:≡ : Equivalence (_≡_ ∶ Relation ℓ A)
    Equivalence:≡ = intro

cong :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    (f : A → B)
    {x y : A}
  → x ≡ y
  → f x ≡ f y
cong _ refl = refl

module ≡Reasoning {ℓ₁} {A : Type ℓ₁} where
  open EquivalenceReasoning (_≡_ ∶ Relation ℓ₁ A)
    public
    hiding ( _≡⟨_⟩_
           )
    renaming ( _~⟨_⟩_   to _≡⟨_⟩_
             ; _~⟨⟩_    to _≡⟨⟩_
             ; _~⟨_⟩⁻¹_ to _≡⟨_⟩⁻¹_
             )

  in-context :
    ∀ {ℓ₂}
      {B : Type ℓ₂}
      (f : B → A)
      {x y : B}
    → x ≡ y
    → f x ≡ f y
  in-context = cong
  syntax in-context f γ = γ |in-context f

subst :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} (B : A → Type ℓ₂)
    {x y : A}
  → x ≡ y
  → B x
  → B y
subst B γ u = ≡.rec B u _ γ

module _ {ℓ} {A : Type ℓ} where

  infix 4 _≢_

  _≢_ : Relation ℓ A
  x ≢ y = ¬ (x ≡ y)

record Reveal_·_is_
    {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : A → Type ℓ₂}
    (f : (x : A) → B x) (x : A) (y : B x) : Type (ℓ₁ ⊔ ℓ₂) where
  constructor [_]
  field eq : f x ≡ y

inspect :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    (f : (x : A) → B x)
    (x : A)
  → Reveal f · x is f x
inspect f x = [ refl ]

≡↓-const-intro :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {x y : A} (γ : x ≡ y)
    {u v : B}
  → u ≡ v
  → subst (const B) γ u ≡ v
≡↓-const-intro refl γ = γ

≡↓-const-elim :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {B : Type ℓ₂}
    {x y : A} (γ : x ≡ y)
    {u v : B}
  → subst (const B) γ u ≡ v    
  → u ≡ v
≡↓-const-elim refl γ = γ
