module Finite.Partition where

open import Base.Type
open import Base.Pi
open import Base.Relation
open import Base.Maybe
  as M
open import Base.Equality
open import Base.Prop
open import Base.Nat
open import Base.List
  as L

open import Finite.UList
  as UL
open import Finite.UList.NonEmpty
  as UL⁺

open import Finite.Partition.Core
  public
open import Finite.Partition.Pseudo
  as Pseudo
  using ( narrow-partition
        )

module _
    {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    {_~_ : Relation ℓ₂ A} ⦃ _ : ∀ {x y} → Prop (x ~ y) ⦄ ⦃ _ : Equivalence _~_ ⦄
    where

  open ≡Reasoning
  open RelativeEquivalenceClass
  open RelativePartition

  total-length : ∀ {xs} → RelativePartition A _~_ xs → ℕ
  total-length = L.sum ∘ L.map (UL⁺.length ∘ elements) ∘ classes

  total-length-pseudo : ∀ {xs} (p : RelativePartition A _~_ xs) → total-length p ≡ Pseudo.total-length (Pseudo.from-RelativePartition p)
  total-length-pseudo p =
      total-length p
        ≡⟨⟩
      L.sum (L.map (UL⁺.length ∘ elements) (classes p))
        ≡⟨⟩
      L.fold _+_ 0 (L.map (UL⁺.length ∘ elements) (classes p))
        ≡⟨ L.fold-map (UL⁺.length ∘ elements) _+_ 0 (classes p) ⟩
      L.fold (λ c n → UL⁺.length (elements c) + n) 0 (classes p)
        ≡⟨⟩
      L.fold (λ c n → M.rec 0 (UL⁺.length ∘ elements) (just c) + n) 0 (classes p)
        ≡⟨⟩
      L.fold (λ c n → Pseudo.class-length (just c) + n) 0 (classes p)
        ≡⟨ L.fold-map (Pseudo.class-length ∘ just) _+_ 0 (classes p) ⟩⁻¹
      L.fold _+_ 0 (L.map (Pseudo.class-length ∘ just) (classes p))
        ≡⟨ L.map-∘ Pseudo.class-length just (classes p) |in-context L.fold _+_ 0 ⟩
      L.fold _+_ 0 (L.map Pseudo.class-length (L.map just (classes p)))
        ≡⟨⟩
      Pseudo.total-length (Pseudo.from-RelativePartition p)
        ∎

  total-length-is-length : ∀ {xs} (p : RelativePartition A _~_ xs) → total-length p ≡ UL.length xs
  total-length-is-length {xs} p =
      total-length p
    ≡⟨ total-length-pseudo p ⟩
      Pseudo.total-length (Pseudo.from-RelativePartition p)
    ≡⟨ Pseudo.total-length-is-length (Pseudo.from-RelativePartition p) ⟩
      UL.length xs
    ∎
