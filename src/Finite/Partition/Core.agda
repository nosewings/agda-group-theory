module Finite.Partition.Core where

open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Type.Negation.Double
  as ¬¬
  hiding ( intro
         )
open import Base.Level
  hiding ( zero
         ; succ
         )
open import Base.Pi
open import Base.Sigma
open import Base.Product
open import Base.Sum
  as ⊎
open import Base.Relation
open import Base.Equality
  hiding ( refl
         )
open import Base.Decide
open import Base.IsProp
open import Base.WellFounded
  as WellFounded
open import Base.Nat
  hiding ( refl
         )
open import Base.List
  as L
open import Base.List.All
  as L∀
open import Base.List.One
  as L∃!

open import Finite.UList
  as UL
open import Finite.UList.All
  as UL∀
open import Finite.UList.Any
  as UL∃
open import Finite.UList.Sublist
import Finite.UList.Partition
  as ULP
open import Finite.UList.NonEmpty
  as UL⁺

module _
    {ℓ₁ ℓ₂}
    (A : Type ℓ₁)
    (_~_ : Relation ℓ₂ A) ⦃ _ : ∀ {x y} → IsProp (x ~ y) ⦄ ⦃ _ : Equivalence _~_ ⦄
    where

  private
    _≁_ : Relation ℓ₂ A
    x ≁ y = ¬ (x ~ y)

  record RelativeEquivalenceClass (xs : UList A) : Type (ℓ₁ ⊔ ℓ₂) where
    constructor intro
    field
      elements          : UList⁺ A
      elements-sublist  : UL⁺.to-UList elements ≼ xs
      elements-related  : UL∀.All (_~ UL⁺.head elements) (UL⁺.tail elements)
      elements-complete : UL∀.All (λ x → (x UL⁺.∈ elements) ⊎ (x ≁ UL⁺.head elements)) xs
  open RelativeEquivalenceClass

  record RelativePartition (xs : UList A) : Type (ℓ₁ ⊔ ℓ₂) where
    constructor intro
    field
      classes          : List (RelativeEquivalenceClass xs)
      classes-complete : UL∀.All (λ x → L∃!.One ((x ~_) ∘ UL⁺.head ∘ elements) classes) xs

open RelativeEquivalenceClass
open RelativePartition

module _
    {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    {_~_ : Relation ℓ₂ A} ⦃ _ : ∀ {x y} → IsProp (x ~ y) ⦄ ⦃ _ : Equivalence _~_ ⦄
    where

  elements-related-full : ∀ {xs} (c : RelativeEquivalenceClass A _~_ xs) → UL⁺.All (_~ UL⁺.head (elements c)) (elements c)
  elements-related-full c = refl ∷ elements-related c

  elements-with-rel-proofs : ∀ {xs} (c : RelativeEquivalenceClass A _~_ xs) → UList (Σ A (_~ (UL⁺.head (elements c))))
  elements-with-rel-proofs c = UL∀.to-UList (elements-related-full c)

module _
    {ℓ₁ ℓ₂}
    (A : Type ℓ₁)
    (_~_ : Relation ℓ₂ A) ⦃ _ : ∀ {x y} → IsProp (x ~ y) ⦄ ⦃ _ : Equivalence _~_ ⦄ ⦃ _ : ∀ {x y} → Decide (x ~ y) ⦄
    where

  private
    _≁_ : Relation ℓ₂ A
    x ≁ y = ¬ (x ~ y)

  open ULP.Partition

  -- Given a UList xs, give a partition relative to xs. This uses well-founded
  -- induction on the length of xs.
  relative-partition : (xs : UList A) → RelativePartition A _~_ xs
  relative-partition = WellFounded.induction (on-wf UL.length <′-wf) _ step where

    step : (xs : UList A)
         → ((ys : UList A) → UL.length ys <′ UL.length xs → RelativePartition A _~_ ys)
         → RelativePartition A _~_ xs
    step []                rec = intro [] []
    step (x ∷ xs and x∉xs) rec = rp′ where

      -- Partition xs into two sublists: pass(p) and fail(p). pass(p) is a
      -- sublist containing all elements related to x, and fail(p) is a sublist
      -- containing all elements not related to x.
      p : ULP.Partition (_~ x) xs
      p = ULP.partition (_~ x) xs

      -- The new equivalence class.
      c′ : RelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs)
      elements          c′ = x ∷ pass p and ≼-preserves-∉ (pass-is-sublist p) x∉xs
      elements-related  c′ = pass-passes p
      elements-sublist  c′ = x ∷ pass-is-sublist p
      elements-complete c′ = inₗ (here refl) ∷ UL∀.map (λ _ → ⊎.map there (UL∀.apply (fail-fails p))) (conservation p)

      -- The recursive call, which yields a partition relative to
      -- fail(p). Remember that fail(p) is essentially xs∖pass(p), and pass(p)
      -- comprises the elements of the new equivalence class, so fail(p) is just
      -- all the elements we have yet to process.
      rp : RelativePartition A _~_ (fail p)
      rp = rec (fail p) (succ≤′succ (≼⇒length≤′ (fail-is-sublist p)))

      -- A lemma we will use several times: x is not related to the head of any
      -- element list of any equivalence class relative to fail(p).
      x≁head : (c : RelativeEquivalenceClass A _~_ (fail p)) → x ≁ UL⁺.head (elements c)
      x≁head c = sym (UL∀.head (≼-preserves-All (elements-sublist c) (fail-fails p)))

      -- Go over the equivalence classes we received from the recursive call and
      -- generalize them so that they are relative to the whole list.
      cs′ : List (RelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs))
      cs′ = L.map generalize (classes rp) where
        generalize : RelativeEquivalenceClass A _~_ (fail p) → RelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs)
        elements          (generalize c) = elements c
        elements-related  (generalize c) = elements-related c
        elements-sublist  (generalize c) = elements-sublist c ⟨ trans ⟩ x ∺ fail-is-sublist p
        elements-complete (generalize c) =
            inᵣ (x≁head c) ∷ ULP.disjunct-elim p (UL∀.map (λ a → inᵣ ∘ a~x⇒y≁head a) (pass-passes p)) (elements-complete c) where
          a~x⇒y≁head : ∀ a → a ~ x → a ≁ UList⁺.head (elements c)
          a~x⇒y≁head _ a~x = ¬.contramap (trans (sym a~x)) (x≁head c)

      -- The new partition.
      rp′ : RelativePartition A _~_ (x ∷ xs and x∉xs)
      classes          rp′ = c′ ∷ cs′
      classes-complete rp′ =
          here refl (L∀.map-compat x≁head _) ∷ ULP.disjunct-elim p (UL∀.map rel-x (pass-passes p))
                                                                   (UL∀.map generalize-classes-rel (classes-complete rp)) where

        rel-x :
          ∀ a
          → a ~ x
          → L∃!.One ((a ~_) ∘ UL⁺.head ∘ elements) (c′ ∷ cs′)
        rel-x a a~x = here a~x (L∀.map-compat (¬.contramap (trans (sym a~x)) ∘ x≁head) _)

        generalize-classes-rel :
          ∀ a
          → L∃!.One ((a ~_) ∘ UL⁺.head ∘ elements) (classes rp)
          → L∃!.One ((a ~_) ∘ UL⁺.head ∘ elements) (c′ ∷ cs′)
        generalize-classes-rel a ϕ = nothere a≁x (L∃!.map-over-map id id ϕ) where
          a≁x : a ≁ x
          a≁x = let (c , _ , ψ) = L∃!.extract ϕ
                in ¬.contramap (λ a~x → sym a~x ⟨ trans ⟩ ψ) (x≁head c)

module _
    {ℓ₁ ℓ₂}
    (A : Type ℓ₁) ⦃ _ : Finite A ⦄
    (_~_ : Relation ℓ₂ A) ⦃ _ : ∀ {x y} → IsProp (x ~ y) ⦄ ⦃ _ : Equivalence _~_ ⦄
    where

  EquivalenceClass = RelativeEquivalenceClass A _~_ (elements-of A)
  Partition        = RelativePartition        A _~_ (elements-of A)

module _
    {ℓ₁ ℓ₂}
    (A : Type ℓ₁) ⦃ _ : Finite A ⦄
    (_~_ : Relation ℓ₂ A) ⦃ _ : ∀ {x y} → IsProp (x ~ y) ⦄ ⦃ _ : Equivalence _~_ ⦄ ⦃ _ : ∀ {x y} → Decide (x ~ y) ⦄
    where

  partition : Partition A _~_
  partition = relative-partition A _~_ (elements-of A)

module _
    {ℓ₁ ℓ₂}
    {A : Type ℓ₁} ⦃ _ : Finite A ⦄
    {_~_ : Relation ℓ₂ A} ⦃ _ : ∀ {x y} → IsProp (x ~ y) ⦄ ⦃ eq : Equivalence _~_ ⦄
    where

  -- The elements of an equivalence class, together with their relatedness
  -- proofs, form an enumeration of the relevant Σ-type. This is only provable
  -- because the relation is required to be propositional.
  elements-with-rel-proofs-Enumeration : ∀ c → Enumeration (elements-with-rel-proofs ⦃ _ ⦄ ⦃ eq ⦄ c)
  elements-with-rel-proofs-Enumeration c = intro
      λ{ (x , x~head) → let x∈A        = locate-in (elements-of A) x
                            x∈elements = ⊎.left (UL∀.apply (elements-complete c) x∈A) (¬¬.intro x~head)
                        in to-UList-prop-lookup (elements-related-full c) x∈elements x~head
       }
