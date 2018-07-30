module Algebra.Group.Lagrange where

open import Base.Level
  hiding ( zero
         )
open import Base.Type
open import Base.Type.Equivalence
  as ≅
  using ( _≅_
        ; to-inj
        ; from-inj
        ; to-surj
        ; from-surj
        )
open import Base.Pi
open import Base.Sigma
open import Base.Product
open import Base.Relation
open import Base.Equality
  as ≡
  hiding ( refl
         )
open import Base.Prop
open import Base.Decide
open import Base.Nat
  as ℕ
open import Base.List
  as List

open import Finite.UList
  as UList
open import Finite.UList.All
  as UListAll
open import Finite.UList.Image
open import Finite.UList.NonEmpty
  as UList⁺
open import Finite.Relationships
open import Finite.Partition

open import Algebra.Group

module LeftCosets
    {ℓ₁ ℓ₂}
    (G : Type ℓ₁) ⦃ _ : Group G ⦄
    (H : Type ℓ₂) ⦃ _ : Group H ⦄
    (ϕ : H → G) ⦃ _ : Monomorphism ϕ ⦄
    where

  open ≡Reasoning

  -- The relation whose equivalence classes are left cosets. This relation is
  -- automatically decidable.
  _~ᴸ_ : Relation (ℓ₁ ⊔ ℓ₂) G
  _~ᴸ_ = λ x y → Σ[ h ] x · ϕ h ≡ y

  instance

    Reflexive:~ᴸ : Reflexive _~ᴸ_
    Reflexive:~ᴸ = Reflexive.intro (ε , aux) where
      abstract
        aux : ∀ {x} → x · ϕ ε ≡ x
        aux {x} =
          x · ϕ ε ≡⟨ homo-ε ϕ |in-context (x ·_) ⟩
          x · ε   ≡⟨ right-id x ⟩
          x       ∎

    Symmetric:~ᴸ : Symmetric _~ᴸ_
    Symmetric:~ᴸ = Symmetric.intro λ{ (h , x·ϕ[h]≡y) → h ⁻¹ , aux h x·ϕ[h]≡y } where
      abstract
        aux : ∀ {x y} h → x · ϕ h ≡ y → y · ϕ (h ⁻¹) ≡ x
        aux {x} {y} h x·ϕ[h]≡y = right-cancel (ϕ h) $
          (y · ϕ (h ⁻¹)) · ϕ h ≡⟨ assoc y (ϕ (h ⁻¹)) (ϕ h) ⟩
          y · (ϕ (h ⁻¹) · ϕ h) ≡⟨ homo-⁻¹ ϕ h |in-context (λ g → y · (g · ϕ h)) ⟩
          y · (ϕ h ⁻¹ · ϕ h)   ≡⟨ left-inv (ϕ h) |in-context (y ·_) ⟩
          y · ε                ≡⟨ right-id y ⟩
          y                    ≡⟨ x·ϕ[h]≡y ⟩⁻¹
          x · ϕ h              ∎

    Transitive:~ᴸ : Transitive _~ᴸ_
    Transitive:~ᴸ = Transitive.intro λ{ (h₁ , x·ϕ[h₁]≡y) (h₂ , y·ϕ[h₂]≡z) → (h₁ · h₂) , aux h₁ h₂ x·ϕ[h₁]≡y y·ϕ[h₂]≡z  } where
      abstract
        aux : ∀ {x y z} h₁ h₂ → x · ϕ h₁ ≡ y → y · ϕ h₂ ≡ z → x · ϕ (h₁ · h₂) ≡ z
        aux {x} {y} {z} h₁ h₂ x·ϕ[h₁]≡y y·ϕ[h₂]≡z =
          x · ϕ (h₁ · h₂)   ≡⟨ homo-· ϕ h₁ h₂ |in-context (x ·_) ⟩
          x · (ϕ h₁ · ϕ h₂) ≡⟨ assoc x (ϕ h₁) (ϕ h₂) ⟩⁻¹
          (x · ϕ h₁) · ϕ h₂ ≡⟨ x·ϕ[h₁]≡y |in-context (_· ϕ h₂) ⟩
          y · ϕ h₂          ≡⟨ y·ϕ[h₂]≡z ⟩
          z                 ∎

    Preorder:~ᴸ : Preorder _~ᴸ_
    Preorder:~ᴸ = Preorder.intro

    Equivalence:~ᴸ : Equivalence _~ᴸ_
    Equivalence:~ᴸ = Equivalence.intro

    -- It is a mere proposition whether elements are in the same left
    -- coset. That is, for any two elements x,y:G, any two proofs that x~ᴸy are
    -- themselves equal. This is due to the injectivity of composition with one
    -- element fixed and the injectivity of ϕ, as well as the fact that we have
    -- axiom K enabled.
    Prop:~ᴸ : ∀ {x y} → Prop (x ~ᴸ y)
    Prop:~ᴸ = Prop.intro (λ{ (_ , γ) (_ , η) → Σ≡-intro-prop _ _ (aux γ η) }) where
      abstract
        aux : ∀ {x y h₁ h₂}
               → x · ϕ h₁ ≡ y
               → x · ϕ h₂ ≡ y
               → h₁ ≡ h₂
        aux {x} {y} γ η = let ε = γ ⟨ trans ⟩ sym η
                              τ = left-cancel x ε
                          in Monomorphism.injective ! τ

  ~ᴸ-map : ∀ g → Image ϕ → Σ G (g ~ᴸ_)
  ~ᴸ-map g (x , h , ϕ[h]≡x) = g · x , h , cong (g ·_) ϕ[h]≡x

  abstract
    ~ᴸ-map-injective : ∀ g → Injective (~ᴸ-map g)
    ~ᴸ-map-injective g γ = let (η , ε) = ×≡-elim _ _ (proj₁ (Σ≡-elim _ _ (from-inj Σ-assoc γ)))
                           in to-inj Σ-assoc (Σ≡-intro-prop _ _ (×≡-intro _ _ (left-cancel g η , ε)))

  ~ᴸ-map-surjective : ∀ g → SplitSurjective (~ᴸ-map g)
  proj₁ (~ᴸ-map-surjective g (x , h , γ)) = g ⁻¹ · x , h , left-invert γ
  proj₂ (~ᴸ-map-surjective g (x , h , γ)) = to-inj Σ-assoc (Σ≡-intro _ _ ((×≡-intro _ _ (aux , _≡_.refl)) , prop _ _)) where
    abstract
      aux : g · (g ⁻¹ · x) ≡ x
      aux = g · (g ⁻¹ · x) ≡⟨ assoc g (g ⁻¹) x ⟩⁻¹
            (g · g ⁻¹) · x ≡⟨ right-inv g |in-context (_· x) ⟩
            ε · x          ≡⟨ left-id x ⟩
            x              ∎

  -- As a consequence, any equivalence class of ~ᴸ is equivalent (as a type) to
  -- Image(ϕ).
  ≅Image : ∀ g → Σ G (_~ᴸ g) ≅ Image ϕ
  ≅Image g =
      Σ-proj₂-≅-intro (λ x → Symmetric-Prop-≅ _~ᴸ_ x g) ⟨ ≅.trans ⟩ ≅.sym (≅.from-inj-and-surj (~ᴸ-map-injective g) (~ᴸ-map-surjective g))

module _ {ℓ₁ ℓ₂}
         (G : Type ℓ₁) ⦃ _ : Group G ⦄ ⦃ _ : Finite G ⦄
         (H : Type ℓ₂) ⦃ _ : Group H ⦄ ⦃ _ : Finite H ⦄
         (ϕ : H → G) ⦃ _ : Monomorphism ϕ ⦄
         where

  open ≡Reasoning
  open RelativeEquivalenceClass
  open RelativePartition
  open LeftCosets G H ϕ

  private

    instance
      Finite-Image[ϕ] : Finite (Image ϕ)
      Finite-Image[ϕ] = Finite:InjectiveImage ϕ (Monomorphism.injective !)

    -- Every equivalence class of ~ᴸ has the same size as H.
    abstract
      ~ᴸ-class-size : (c : EquivalenceClass G _~ᴸ_) → UList⁺.length (elements c) ≡ size-of H
      ~ᴸ-class-size c =
          UList⁺.length (elements c)
            ≡⟨ UListAll.to-UList-length (elements-related-full c) ⟩⁻¹
          UList.length (elements-with-rel-proofs c)
            ≡⟨ UListEnumerations-≅-sizes (elements-with-rel-proofs c) (elements-with-rel-proofs-Enumeration c)
                                         (elements-of (Image ϕ))      (Enumeration:InjectiveImage _ injective)
                                         (≅Image (UList⁺.head (elements c)))
             ⟩
          size-of (Image ϕ)
            ≡⟨ Image-size ϕ injective ⟩
          size-of H
            ∎

    -- Partition G into the equivalence classes of ~ᴸ.
    ~ᴸ-partition = partition G _~ᴸ_

  -- The theorem itself.
  lagrange : Σ[ n ] size-of G ≡ n * size-of H
  proj₁ lagrange = List.length (classes ~ᴸ-partition)
  proj₂ lagrange = aux where
    abstract
      aux = size-of G
              ≡⟨ total-length-is-length ~ᴸ-partition ⟩⁻¹
            total-length ~ᴸ-partition
              ≡⟨⟩
            List.sum (List.map (UList⁺.length ∘ elements) (classes ~ᴸ-partition))
              ≡⟨ List.map-≐ ~ᴸ-class-size (classes ~ᴸ-partition) |in-context List.sum ⟩
            List.sum (List.map (const (size-of H)) (classes ~ᴸ-partition))
              ≡⟨⟩
            List.fold _+_ zero (List.map (const (size-of H)) (classes ~ᴸ-partition))
              ≡⟨ List.fold-map (const (size-of H)) _+_ zero (classes ~ᴸ-partition) ⟩
            List.fold (λ _ n → size-of H + n) zero (classes ~ᴸ-partition)
              ≡⟨ List.fold-ℕ-fold (size-of H +_) zero (classes ~ᴸ-partition) ⟩
            ℕ.fold (size-of H +_) zero (List.length (classes ~ᴸ-partition))
              ≡⟨ ℕ.*-fold (List.length (classes ~ᴸ-partition)) (size-of H) ⟩⁻¹
            List.length (classes ~ᴸ-partition) * size-of H
              ∎
