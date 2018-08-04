module Algebra.Group where

open import Base.Level
open import Base.Type
open import Base.Pi
open import Base.Sigma
open import Base.Relation
open import Base.Equality
open import Base.Pi.Operation

record Group {ℓ} (G : Type ℓ) : Type ℓ where
  infix 6 _⁻¹
  infix 5 _·_
  field
    _·_ : Op₂ G
    ε : Op₀ G
    _⁻¹ : Op₁ G
    assoc : Associative _·_
    left-id : LeftIdentity _·_ ε
    right-id : RightIdentity _·_ ε
    left-inv : LeftInverse _·_ ε _⁻¹
    right-inv : RightInverse _·_ ε _⁻¹
open Group ⦃...⦄
  public

module _ {ℓ} {G : Type ℓ} ⦃ _ : Group G ⦄ where

  open ≡Reasoning

  abstract

    left-cancel : LeftCancellative (_·_ ∶ Op₂ G)
    left-cancel {y₁} {y₂} x xy₁≡xy₂ =
        y₁              ≡⟨ left-id y₁ ⟩⁻¹
        ε · y₁          ≡⟨ left-inv x |in-context (_· y₁) ⟩⁻¹
        (x ⁻¹ · x) · y₁ ≡⟨ assoc (x ⁻¹) x y₁ ⟩
        x ⁻¹ · (x · y₁) ≡⟨ xy₁≡xy₂ |in-context (x ⁻¹ ·_) ⟩
        x ⁻¹ · (x · y₂) ≡⟨ assoc (x ⁻¹) x y₂ ⟩⁻¹
        (x ⁻¹ · x) · y₂ ≡⟨ left-inv x |in-context (_· y₂) ⟩
        ε · y₂          ≡⟨ left-id y₂ ⟩
        y₂              ∎

    right-cancel : RightCancellative (_·_ ∶ Op₂ G)
    right-cancel {x₁} {x₂} y x₁y≡x₂y =
        x₁              ≡⟨ right-id x₁ ⟩⁻¹
        x₁ · ε          ≡⟨ right-inv y |in-context (x₁ ·_) ⟩⁻¹
        x₁ · (y · y ⁻¹) ≡⟨ assoc x₁ y (y ⁻¹) ⟩⁻¹
        (x₁ · y) · y ⁻¹ ≡⟨ x₁y≡x₂y |in-context (_· y ⁻¹) ⟩
        (x₂ · y) · y ⁻¹ ≡⟨ assoc x₂ y (y ⁻¹) ⟩
        x₂ · (y · y ⁻¹) ≡⟨ right-inv y |in-context (x₂ ·_) ⟩
        x₂ · ε          ≡⟨ right-id x₂ ⟩
        x₂              ∎

    left-id-unique : {g : G} → LeftIdentity _·_ g → g ≡ ε
    left-id-unique {g} ϕ =
        g     ≡⟨ right-id g ⟩⁻¹
        g · ε ≡⟨ ϕ ε ⟩
        ε     ∎

    right-id-unique : {g : G} → RightIdentity _·_ g → g ≡ ε
    right-id-unique {g} ϕ =
        g     ≡⟨ left-id g ⟩⁻¹
        ε · g ≡⟨ ϕ ε ⟩
        ε     ∎

    left-invert : {x y z : G} → x · y ≡ z → y ≡ x ⁻¹ · z
    left-invert {x} {y} {z} x·y≡z = left-cancel x $
        x · y          ≡⟨ x·y≡z ⟩
        z              ≡⟨ left-id z ⟩⁻¹
        ε · z          ≡⟨ right-inv x |in-context (_· z) ⟩⁻¹
        (x · x ⁻¹) · z ≡⟨ assoc x (x ⁻¹) z ⟩
        x · (x ⁻¹ · z) ∎
      
    right-invert : {x y z : G} → x · y ≡ z → x ≡ z · y ⁻¹
    right-invert {x} {y} {z} x·y≡z = right-cancel y $
      x · y          ≡⟨ x·y≡z ⟩
      z              ≡⟨ right-id z ⟩⁻¹
      z · ε          ≡⟨ left-inv y |in-context (z ·_) ⟩⁻¹
      z · (y ⁻¹ · y) ≡⟨ assoc z (y ⁻¹) y ⟩⁻¹
      (z · y ⁻¹) · y ∎

    left-inv-unique : {g x : G} → x · g ≡ ε → x ≡ g ⁻¹
    left-inv-unique {g} {x} x·g≡ε =
        x        ≡⟨ right-invert x·g≡ε ⟩
        ε · g ⁻¹ ≡⟨ left-id (g ⁻¹) ⟩
        g ⁻¹     ∎

    right-inv-unique : {g x : G} → g · x ≡ ε → x ≡ g ⁻¹
    right-inv-unique {g} {x} g·x≡ε =
        x        ≡⟨ left-invert g·x≡ε ⟩
        g ⁻¹ · ε ≡⟨ right-id (g ⁻¹) ⟩
        g ⁻¹     ∎

    reversal : (x y : G) → (x · y) ⁻¹ ≡ y ⁻¹ · x ⁻¹
    reversal x y = sym $ right-inv-unique $
        (x · y) · (y ⁻¹ · x ⁻¹) ≡⟨ assoc x y (y ⁻¹ · x ⁻¹) ⟩
        x · (y · (y ⁻¹ · x ⁻¹)) ≡⟨ assoc y (y ⁻¹) (x ⁻¹) |in-context (x ·_) ⟩⁻¹
        x · ((y · y ⁻¹) · x ⁻¹) ≡⟨ right-inv y |in-context (λ g → x · (g · x ⁻¹)) ⟩
        x · (ε · x ⁻¹)          ≡⟨ left-id (x ⁻¹) |in-context (x ·_) ⟩
        x · x ⁻¹                ≡⟨ right-inv x ⟩
        ε                       ∎

    idempotent-is-id : {g : G} → Idempotent _·_ g → g ≡ ε
    idempotent-is-id {g} gg≡g = left-cancel g $
        g · g ≡⟨ gg≡g ⟩
        g     ≡⟨ right-id g ⟩⁻¹
        g · ε ∎

  left-trans[_] : G → G → G
  left-trans[ g ] = g ·_

  right-trans[_] : G → G → G
  right-trans[ g ] = _· g

  abstract

    left-trans-inj : ∀ g → Injective left-trans[ g ]
    left-trans-inj g = left-cancel g

    right-trans-inj : ∀ g → Injective right-trans[ g ]
    right-trans-inj g = right-cancel g

  left-trans-surj : ∀ g → SplitSurjective left-trans[ g ]
  left-trans-surj g x = (g ⁻¹ · x) , aux where
    abstract
      aux : g · (g ⁻¹ · x) ≡ x
      aux =
        g · (g ⁻¹ · x) ≡⟨ assoc g (g ⁻¹) x ⟩⁻¹
        (g · g ⁻¹) · x ≡⟨ right-inv g |in-context (_· x) ⟩
        ε · x          ≡⟨ left-id x ⟩
        x              ∎

  right-trans-surj : ∀ g → SplitSurjective right-trans[ g ]
  right-trans-surj g x = (x · g ⁻¹) , aux where
    abstract
      aux : (x · g ⁻¹) · g ≡ x
      aux =
        (x · g ⁻¹) · g ≡⟨ assoc x (g ⁻¹) g ⟩
        x · (g ⁻¹ · g) ≡⟨ left-inv g |in-context (x ·_) ⟩
        x · ε          ≡⟨ right-id x ⟩
        x              ∎

record Homomorphism
    {ℓ₁ ℓ₂}
    {G₁ : Type ℓ₁} ⦃ _ : Group G₁ ⦄
    {G₂ : Type ℓ₂} ⦃ _ : Group G₂ ⦄
    (ϕ : G₁ → G₂) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    homo-· : (x y : G₁) → ϕ (x · y) ≡ ϕ x · ϕ y

module _
    {ℓ₁ ℓ₂}
    {G₁ : Type ℓ₁} ⦃ _ : Group G₁ ⦄
    {G₂ : Type ℓ₂} ⦃ g₂ : Group G₂ ⦄
    (ϕ : G₁ → G₂) ⦃ _ : Homomorphism ϕ ⦄ where

  open ≡Reasoning

  abstract

    homo-· : (x y : G₁) → ϕ (x · y) ≡ ϕ x · ϕ y
    homo-· x y = Homomorphism.homo-· !!! x y

    homo-ε : ϕ ε ≡ (ε ∶ G₂)
    homo-ε = idempotent-is-id $
        ϕ ε · ϕ ε ≡⟨ homo-· ε ε ⟩⁻¹
        ϕ (ε · ε) ≡⟨ right-id ε |in-context ϕ ⟩
        ϕ ε       ∎

    homo-⁻¹ : (x : G₁) → ϕ (x ⁻¹) ≡ (ϕ x) ⁻¹
    homo-⁻¹ x = right-inv-unique $
        ϕ x · ϕ (x ⁻¹) ≡⟨ homo-· x (x ⁻¹) ⟩⁻¹
        ϕ (x · x ⁻¹)   ≡⟨ right-inv x |in-context ϕ ⟩
        ϕ ε            ≡⟨ homo-ε ⟩
        ε              ∎

record Monomorphism
    {ℓ₁ ℓ₂}
    {G₁ : Type ℓ₁} ⦃ _ : Group G₁ ⦄
    {G₂ : Type ℓ₂} ⦃ _ : Group G₂ ⦄
    (ϕ : G₁ → G₂) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    ⦃ homomorphism ⦄ : Homomorphism ϕ
    ⦃ injective ⦄    : Injective ϕ
open Monomorphism ⦃...⦄
  public
