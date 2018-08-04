module Finite.Partition.Pseudo where

open import Base.Level
  hiding ( zero
         ; succ
         )
open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Pi.Operation
open import Base.Sum
  as ⊎
open import Base.Maybe
  as M
open import Base.Equality
open import Base.Nat
  as ℕ
open import Base.List
  as L
open import Base.List.All
  as L∀
open import Base.List.One
  as L∃!
open import Base.Relation
  as Relation
  hiding ( refl
         )
open import Base.Prop

open import Finite.UList
  as UL
open import Finite.UList.All
  as UL∀
open import Finite.UList.Any
  as UL∃
open import Finite.UList.Sublist
open import Finite.UList.NonEmpty
  as UL⁺

open import Finite.Partition.Core

open ≡Reasoning

private
  abstract

    stupid-lemma-lemma :
      ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        {A : Type ℓ₁} (B : A → Type ℓ₂) (P : ∀ {x} → B x → Type ℓ₃) {C : Type ℓ₄}
        (_·_ : Op₂ C)
        (e : C)
        {a₁ a₂ : A}
        (f : B a₁ → B a₂)
        (g : ∀ {x} → B x → C)
      → ((x : B a₁) → P x → g x ≡ g (f x))
      → {xs : List (B a₁)}
      → L∀.All P xs
      → L.foldr _·_ e (L.map g xs) ≡ L.foldr _·_ e (L.map (g ∘ f) xs)
    stupid-lemma-lemma B P _·_ e f g ϕ []                   = refl
    stupid-lemma-lemma B P _·_ e f g ϕ {x ∷ xs} (Px ∷ ∀xsP) =
        L.foldr _·_ e (L.map g (x ∷ xs))
          ≡⟨⟩
        L.foldr _·_ e (g x ∷ L.map g xs)
          ≡⟨⟩
        g x · L.foldr _·_ e (L.map g xs)
          ≡⟨ ϕ x Px |in-context (_· L.foldr _·_ e (L.map g xs)) ⟩
        g (f x) · L.foldr _·_ e (L.map g xs)
          ≡⟨ stupid-lemma-lemma B P _·_ e f g ϕ ∀xsP |in-context (g (f x) ·_) ⟩
        g (f x) · L.foldr _·_ e (L.map (g ∘ f) xs)
          ≡⟨⟩
        L.foldr _·_ e (g (f x) ∷ L.map (g ∘ f) xs)
          ≡⟨⟩
        L.foldr _·_ e (L.map (g ∘ f) (x ∷ xs))
          ∎

    stupid-lemma :
      ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
        {A : Type ℓ₁} (B : A → Type ℓ₂) (P : ∀ {a} → B a → Type ℓ₃) {C : Type ℓ₄}
        (_·_ : Op₂ C)
      → Associative _·_
      → Commutative _·_
      → (e : C)
        {a₁ a₂ : A}
        (f : B a₁ → B a₂)
        (g : ∀ {a} → B a → C)
        (c : C)
      → ((x : B a₁) →   P x → g x ≡ c · g (f x))
      → ((x : B a₁) → ¬ P x → g x ≡     g (f x))
      → {xs : List (B a₁)}
      → L∃!.One P xs
      → L.foldr _·_ e (L.map g xs) ≡ c · L.foldr _·_ e (L.map (g ∘ f) xs)
    stupid-lemma B P _·_ assoc comm e f g c ϕ ψ (here {x} {xs} Px ∀xs¬P) =
        L.foldr _·_ e (L.map g (x ∷ xs))
          ≡⟨⟩
        L.foldr _·_ e (g x ∷ L.map g xs)
          ≡⟨⟩
        g x · L.foldr _·_ e (L.map g xs)
          ≡⟨ ϕ x Px |in-context (_· L.foldr _·_ e (L.map g xs)) ⟩
        (c · g (f x)) · L.foldr _·_ e (L.map g xs)
          ≡⟨ stupid-lemma-lemma B (¬_ ∘ P) _·_ e f g ψ ∀xs¬P |in-context ((c · g (f x)) ·_) ⟩
        (c · g (f x)) · L.foldr _·_ e (L.map (g ∘ f) xs)
          ≡⟨ assoc c (g (f x)) (L.foldr _·_ e (L.map (g ∘ f) xs)) ⟩
        c · (g (f x) · L.foldr _·_ e (L.map (g ∘ f) xs))
          ≡⟨⟩
        c · L.foldr _·_ e (g (f x) ∷ L.map (g ∘ f) xs)
          ≡⟨⟩
        c · L.foldr _·_ e (L.map (g ∘ f) (x ∷ xs))
          ∎
    stupid-lemma B P _·_ assoc comm e f g c ϕ ψ (nothere {x} {xs} ¬Px ∃!xsP) =
        L.foldr _·_ e (L.map g (x ∷ xs))
          ≡⟨⟩
        L.foldr _·_ e (g x ∷ L.map g xs)
          ≡⟨⟩
        g x · L.foldr _·_ e (L.map g xs)
          ≡⟨ ψ x ¬Px |in-context (_· L.foldr _·_ e (L.map g xs)) ⟩
        g (f x) · L.foldr _·_ e (L.map g xs)
          ≡⟨ stupid-lemma B P _·_ assoc comm e f g c ϕ ψ ∃!xsP |in-context (g (f x) ·_) ⟩
        g (f x) · (c · L.foldr _·_ e (L.map (g ∘ f) xs))
          ≡⟨ assoc (g (f x)) c (L.foldr _·_ e (L.map (g ∘ f) xs)) ⟩⁻¹
        (g (f x) · c) · L.foldr _·_ e (L.map (g ∘ f) xs)
          ≡⟨ comm (g (f x)) c |in-context (_· L.foldr _·_ e (L.map (g ∘ f) xs)) ⟩
        (c · g (f x)) · L.foldr _·_ e (L.map (g ∘ f) xs)
          ≡⟨ assoc c (g (f x)) (L.foldr _·_ e (L.map (g ∘ f) xs)) ⟩
        c · (g (f x) · L.foldr _·_ e (L.map (g ∘ f) xs))
          ≡⟨⟩
        c · L.foldr _·_ e (g (f x) ∷ L.map (g ∘ f) xs)
          ≡⟨⟩
        c · (L.foldr _·_ e (L.map (g ∘ f) (x ∷ xs)))
          ∎

module _
    {ℓ₁ ℓ₂}
    (A : Type ℓ₁)
    (_~_ : Relation ℓ₂ A) ⦃ _ : ∀ {x y} → Prop (x ~ y) ⦄ ⦃ _ : Equivalence _~_ ⦄
    where

  open RelativeEquivalenceClass

  -- "Pseudo" relative equivalence relations and partitions, which effectively
  -- relax the requirement that an equivalence class be nonempty. Nonempty
  -- pseudo-equivalence classes are still required to be complete (empty ones
  -- are already "vacuously complete"), and all pseudo-partitions are required
  -- to be complete.

  PseudoRelativeEquivalenceClass : UList A → Type (ℓ₁ ⊔ ℓ₂)
  PseudoRelativeEquivalenceClass = Maybe ∘ RelativeEquivalenceClass A _~_

  record PseudoRelativePartition (xs : UList A) : Type (ℓ₁ ⊔ ℓ₂) where
    field
      classes          : List (PseudoRelativeEquivalenceClass xs)
      classes-complete : UL∀.All (λ x → L∃!.One (M.Any ((x ~_) ∘ UL⁺.head ∘ elements)) classes) xs

module _
    {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    {_~_ : Relation ℓ₂ A} ⦃ _ : ∀ {x y} → Prop (x ~ y) ⦄ ⦃ _ : Equivalence _~_ ⦄
    where

  open RelativeEquivalenceClass
  open RelativePartition
  open PseudoRelativePartition

  class-length : ∀ {xs} → PseudoRelativeEquivalenceClass A _~_ xs → ℕ
  class-length = M.rec 0 (UL⁺.length ∘ elements)

  -- Injection.
  from-RelativePartition : ∀ {xs} → RelativePartition A _~_ xs → PseudoRelativePartition A _~_ xs
  classes          (from-RelativePartition p) = L.map some (classes p)
  classes-complete (from-RelativePartition p) =
      UL∀.map (λ x → L∃!.map-over-map here λ{ (here x~head) → x~head }) (classes-complete p)

  -- The total length of a pseudo-partition, defined as the sum of the lengths
  -- of its equivalence classes, where an empty equivalence class has length
  -- 0. Our ultimate aim is to show that, for any pseudo-partition p relative to
  -- a UList xs, total-length(p)≡length(xs).
  total-length : ∀ {xs} → PseudoRelativePartition A _~_ xs → ℕ
  total-length = L.sum ∘ L.map class-length ∘ classes

  abstract

    class-[]-inv : (x : PseudoRelativeEquivalenceClass A _~_ []) → x ≡ none
    class-[]-inv none = refl
    class-[]-inv (some c) with elements-sublist c
    ... | ()

    []-total-length : (p : PseudoRelativePartition A _~_ []) → total-length p ≡ 0
    []-total-length p =
        total-length p
          ≡⟨⟩
        L.sum (L.map class-length (classes p))
          ≡⟨ L.map-≐ (λ m → cong class-length (class-[]-inv m)) (classes p) |in-context L.sum ⟩
        L.sum (L.map (const 0) (classes p))
          ≡⟨⟩
        L.foldr _+_ 0 (L.map (const 0) (classes p))
          ≡⟨ L.foldr-map _+_ 0 (const 0) (classes p) ⟩
        L.foldr (λ _ n → 0 + n) 0 (classes p)
          ≡⟨⟩
        L.foldr (λ _ n → n) 0 (classes p)
          ≡⟨ L.foldr-const-is-ℕ-foldr id 0 (classes p) ⟩
        ℕ.foldr id 0 (L.length (classes p))
          ≡⟨ ℕ.foldr-id 0 (L.length (classes p)) ⟩
        0
          ∎

  -- Narrows a pseudo-equivalence class, removing the front element if
  -- applicable and leaving it essentially unchanged otherwise.
  narrow-class :
    ∀ {x xs x∉xs}
    → PseudoRelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs)
    → PseudoRelativeEquivalenceClass A _~_ xs
  narrow-class {x} {xs} {x∉xs} = M.bind aux where
    aux : RelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs) → Maybe (RelativeEquivalenceClass A _~_ xs)
    aux c with elements c | elements-sublist c | elements-related c | elements-complete c
    ... | e ∷ es and e∉es | _ ∺ [e∷es]≼xs | ∀es[~e] | _ ∷ complete-tail = Maybe.some $ record
        { elements          = e ∷ es and e∉es
        ; elements-sublist  = [e∷es]≼xs
        ; elements-related  = ∀es[~e]
        ; elements-complete = complete-tail
        }
    ... | _ ∷ [] and _ | _ ∷ _ | _ | _ = none
    ... | _ ∷ (e ∷ es and e∉es) and x∉[e∷es] | _ ∷ [e∷es]≼xs | e~x ∷ ∀es[~x] | _ ∷ complete-tail = Maybe.some $ record
        { elements          = e ∷ es and e∉es
        ; elements-sublist  = [e∷es]≼xs
        ; elements-related  = UL∀.map (λ _ → flip trans (sym e~x)) ∀es[~x]
        ; elements-complete =
            UL∀.map-∈ (λ a a∈xs → ⊎.map (UL∃.tail (¬.contramap (λ x≡a → subst (UL∃._∈ xs) (sym x≡a) a∈xs) (∉⇒¬∈ x∉xs)))
                                        (¬.contramap (flip trans e~x)))
                      complete-tail
        }

  -- Narrows an entire pseudo-partition. This will ultimately only remove one
  -- element from one equivalence class.
  narrow-partition :
    ∀ {x xs x∉xs}
    → PseudoRelativePartition A _~_ (x ∷ xs and x∉xs)
    → PseudoRelativePartition A _~_ xs
  classes          (narrow-partition {x} {xs} {x∉xs} p) = L.map narrow-class (classes p)
  classes-complete (narrow-partition {x} {xs} {x∉xs} p) =
      UL∀.map-∈ (λ a a∈xs → L∃!.map-over-map (aux₁ a a∈xs) (aux₂ a a∈xs)) (UL∀.tail (classes-complete p)) where
    aux₁ :
      ∀ a
      → a UL.∈ xs
      → {c : PseudoRelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs)}
      → M.Any ((a ~_) ∘ UL⁺.head ∘ elements) c
      → M.Any ((a ~_) ∘ UL⁺.head ∘ elements) (narrow-class c)
    aux₁ a a∈xs {some c} (here a~head) with elements c | elements-sublist c | elements-related c | elements-complete c
    ... | _            | _ ∺ _ | _       | _ ∷ _             = here a~head
    ... | _ ∷ [] and _ | _ ∷ _ | _       | _ ∷ complete-tail =
        ⊎.rec (λ{ (here refl) → a∈xs ↯ ∉⇒¬∈ x∉xs ; (there ()) })
              (λ a≁x → a~head ↯ a≁x)
              (UL∀.apply complete-tail a∈xs) 
    ... | _            | _ ∷ _ | e~x ∷ _ | _ ∷ _             = here (a~head ⟨ trans ⟩ sym e~x)

    aux₂ :
      ∀ a
      → a UL.∈ xs
      → {c : PseudoRelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs)}
      → M.Any ((a ~_) ∘ UL⁺.head ∘ elements) (narrow-class c)
      → M.Any ((a ~_) ∘ UL⁺.head ∘ elements) c
    aux₂ a a∈xs {none} ()
    aux₂ a a∈xs {some c} ϕ with elements c | elements-sublist c | elements-related c | elements-complete c | inspect elements c
    aux₂ a a∈xs {some c} (here a~e) | _            | _ ∺ _ | _       | _ ∷ _ | [ refl ] = here a~e
    aux₂ a a∈xs {some c} ()         | _ ∷ [] and _ | _ ∷ _ | _       | _     | _
    aux₂ a a∈xs {some c} (here a~e) | _            | _ ∷ _ | e~x ∷ _ | _ ∷ _ | [ refl ] = here (a~e ⟨ trans ⟩ e~x)

  abstract

    narrow-partition-total-length :
      ∀ {x xs x∉xs}
        (p : PseudoRelativePartition A _~_ (x ∷ xs and x∉xs))
      → total-length p ≡ succ (total-length (narrow-partition p))
    narrow-partition-total-length {x} {xs} {x∉xs} p =
        total-length p
          ≡⟨⟩
        L.foldr _+_ 0 (L.map class-length (classes p))
          ≡⟨ stupid-lemma (PseudoRelativeEquivalenceClass A _~_)
                          (M.Any ((x ~_) ∘ UL⁺.head ∘ elements))
                          _+_
                          +-assoc
                          +-comm
                          0
                          narrow-class
                          class-length
                          1
                          aux₁
                          aux₂
                          (UL∀.head (classes-complete p))
           ⟩
        succ (L.foldr _+_ 0 (L.map (class-length ∘ narrow-class) (classes p)))
          ≡⟨ L.map-∘ class-length narrow-class (classes p) |in-context (succ ∘ L.foldr _+_ 0) ⟩
        succ (L.foldr _+_ 0 (L.map class-length (L.map narrow-class (classes p))))
          ≡⟨⟩
        succ (total-length (narrow-partition p))
          ∎ where

      aux₁ :
          (c : PseudoRelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs))
        → M.Any ((x ~_) ∘ UL⁺.head ∘ elements) c
        → class-length c ≡ succ (class-length (narrow-class c))
      aux₁ (some c) (here α) with elements c | elements-sublist c | elements-related c | elements-complete c
      ... | es | _ ∺ ϕ | ψ | β ∷ χ = ⊎.rec (λ ζ → ≼-preserves-∈ ϕ ζ ↯ ∉⇒¬∈ x∉xs) (λ ζ → α ↯ ζ) β
      ... | _ ∷ [] and _ | _ ∷ _ | _ | _ = refl
      ... | x ∷ (e ∷ es and e∉es) and x∉[e∷es] | x ∷ ϕ | e~x ∷ ∀es[~x] | _ ∷ χ = refl

      aux₂ :
          (c : PseudoRelativeEquivalenceClass A _~_ (x ∷ xs and x∉xs))
        → ¬ (M.Any ((x ~_) ∘ UL⁺.head ∘ elements) c)
        → class-length c ≡ class-length (narrow-class c)
      aux₂ none _     = refl
      aux₂ (some c) α with elements c | elements-sublist c | elements-related c | elements-complete c | inspect elements c
      aux₂ (some c) α | es | _ ∺ ϕ | ψ | _ ∷ χ | _ = refl
      aux₂ (some c) α | _ ∷ [] and _ | _ ∷ _ | _ | _ | [ γ ] = here (subst (λ u → x ~ UL⁺.head u) (sym γ) Relation.refl) ↯ α
      aux₂ (some c) α | x ∷ (e ∷ es and e∉es) and x∉[e∷es] | x ∷ ϕ | e~x ∷ ∀es[~x] | _ ∷ χ | [ γ ] =
          here (subst (λ u → x ~ UList⁺.head u) (sym γ) Relation.refl) ↯ α

    total-length-is-length : ∀ {xs} (p : PseudoRelativePartition A _~_ xs) → total-length p ≡ UL.length xs
    total-length-is-length {[]} p = []-total-length p
    total-length-is-length {x ∷ xs and x∉xs} p rewrite narrow-partition-total-length p =
        cong succ (total-length-is-length (narrow-partition p))
