module Base.Relation where

open import Base.Level
  as Level
open import Base.Type
open import Base.Type.Negation
open import Base.Equality.Core
  as ≡
  hiding ( refl
         )
open import Base.Unit.Core
open import Base.FromNat
open import Base.Decide

Relation : ∀ {ℓ₁} ℓ₂ → Type ℓ₁ → Type (ℓ₁ ⊔ Level.succ ℓ₂)
Relation ℓ₂ A = A → A → Type ℓ₂

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} (_~_ : A → A → Type ℓ₂) where

  record Reflexive : Type (ℓ₁ ⊔ ℓ₂) where
    constructor intro
    field
      refl : ∀ {x} → x ~ x
  open Reflexive ⦃...⦄ public

  record Symmetric : Type (ℓ₁ ⊔ ℓ₂) where
    constructor intro
    field
      sym : ∀ {x y} → x ~ y → y ~ x
  open Symmetric ⦃...⦄ public

  record Transitive : Type (ℓ₁ ⊔ ℓ₂) where
    constructor intro
    field
      trans : ∀ {x y z} → x ~ y → y ~ z → x ~ z
  open Transitive ⦃...⦄ public

  record Preorder : Type (ℓ₁ ⊔ ℓ₂) where
    constructor intro
    field
      ⦃ reflexive ⦄ : Reflexive
      ⦃ transitive ⦄ : Transitive
  open Preorder ⦃...⦄ public

  record Equivalence : Type (ℓ₁ ⊔ ℓ₂) where
    constructor intro
    field
      ⦃ preorder ⦄ : Preorder
      ⦃ symmetric ⦄ : Symmetric
  open Equivalence ⦃...⦄ public

instance
  Symmetric:¬ :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁} {_~_ : Relation ℓ₂ A}
      ⦃ _ : Symmetric _~_ ⦄
    → Symmetric (λ x y → ¬ x ~ y)
  Symmetric:¬ = intro (contramap sym)

module PreorderReasoning {ℓ₁ ℓ₂} {A : Type ℓ₁} (_≲_ : Relation ℓ₂ A) ⦃ _ : Preorder _≲_ ⦄ where

  infix  3 _∎
  infixr 2 _≲⟨_⟩_ _≲⟨⟩_ _≡⟨_⟩_

  begin_ : {x y : A} → x ≲ y → x ≲ y
  begin x≲y = x≲y

  _≲⟨_⟩_ : (x {y z} : A) → x ≲ y → y ≲ z → x ≲ z
  _ ≲⟨ x≲y ⟩ y≲z = trans x≲y y≲z

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≲ z → x ≲ z
  _ ≡⟨ ≡.refl ⟩ x≲z = x≲z

  _≲⟨⟩_ : (x {y} : A) → x ≲ y → x ≲ y
  _ ≲⟨⟩ x≲y = x≲y

  _∎ : (x : A) → x ≲ x
  _∎ _ = refl

module EquivalenceReasoning {ℓ₁ ℓ₂} {A : Type ℓ₁} (_~_ : Relation ℓ₂ A) ⦃ _ : Equivalence _~_ ⦄ where

  infixr 2 _~⟨_⟩⁻¹_

  open PreorderReasoning _~_
    public
    renaming ( _≲⟨_⟩_ to _~⟨_⟩_
             ; _≲⟨⟩_  to _~⟨⟩_
             )

  _~⟨_⟩⁻¹_ : (x {y z} : A) → y ~ x → y ~ z → x ~ z
  _ ~⟨ y~x ⟩⁻¹ y~z = trans (sym y~x) y~z

module _ {ℓ} {A : Type ℓ} where

  Trivial : Relation 0 A
  Trivial = λ _ _ → 𝟙

  instance
    Reflexive:Trivial : Reflexive Trivial
    Reflexive:Trivial = _

    Symmetric:Trivial : Symmetric Trivial
    Symmetric:Trivial = _

    Transitive:Trivial : Transitive Trivial
    Transitive:Trivial = _

    Preorder:Trivial : Preorder Trivial
    Preorder:Trivial = _

    Equivalence:Trivial : Equivalence Trivial
    Equivalence:Trivial = _

    Decide:Trivial : ∀ {x y} → Decide (Trivial x y)
    Decide:Trivial = yes _
