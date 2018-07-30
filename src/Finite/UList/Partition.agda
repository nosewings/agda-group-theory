module Finite.UList.Partition where

open import Base.Level
open import Base.Type
open import Base.Type.Negation
open import Base.Pi
open import Base.Sum
  as ⊎
open import Base.Equality
open import Base.Decide

open import Finite.UList.Core
open import Finite.UList.All as UListAll
open import Finite.UList.Sublist

record Partition {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) (xs : UList A) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    pass            : UList A
    fail            : UList A
    pass-passes     : All P        pass
    fail-fails      : All (¬_ ∘ P) fail
    pass-is-sublist : pass ≼ xs
    fail-is-sublist : fail ≼ xs
    conservation    : All (λ x → x ∈ pass ⊎ x ∈ fail) xs
open Partition

partition :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    (P : A → Type ℓ₂)
    ⦃ _ : ∀ {x} → Decide (P x) ⦄
    (xs : UList A)
  → Partition P xs
partition P [] = record { pass            = []
                        ; fail            = []
                        ; pass-passes     = []
                        ; fail-fails      = []
                        ; pass-is-sublist = []
                        ; fail-is-sublist = []
                        ; conservation    = []
                        }
partition P (x ∷ xs and x∉xs) with partition P xs | decide (P x)
... | p | yes Px = record { pass            = x ∷ pass p and ≼-preserves-∉ (pass-is-sublist p) x∉xs
                          ; fail            = fail p
                          ; pass-passes     = Px ∷ pass-passes p
                          ; fail-fails      = fail-fails p
                          ; pass-is-sublist = x ∷ pass-is-sublist p
                          ; fail-is-sublist = x ∺ fail-is-sublist p
                          ; conservation    = inₗ (here refl) ∷ UListAll.map (λ _ → ⊎.rec (inₗ ∘ there) inᵣ) (conservation p)
                          }
... | p | no ¬Px = record { pass            = pass p
                          ; fail            = x ∷ fail p and ≼-preserves-∉ (fail-is-sublist p) x∉xs
                          ; pass-passes     = pass-passes p
                          ; fail-fails      = ¬Px ∷ fail-fails p
                          ; pass-is-sublist = x ∺ pass-is-sublist p
                          ; fail-is-sublist = x ∷ fail-is-sublist p
                          ; conservation    = inᵣ (here refl) ∷ UListAll.map (λ _ → ⊎.rec inₗ (inᵣ ∘ there)) (conservation p)
                          }

module _
    {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
    where

  -- If a proposition holds for all elements of both sublists which comprise a
  -- partition, then it holds for all elements of the original list.
  --
  -- This is by far the ugliest proof in this development (so far).
  --
  -- Actually, the proof itself is really not that bad -- everything falls out
  -- more-or-less naturally. The problem is that we have to pattern match on
  -- every field in the Partition type all at once, so it looks bad. But the
  -- fact that we need all of the fields in order to get the desired result
  -- does sort of show that we are using the correct type.
  disjunct-elim :
      {xs : UList A}
      (p : Partition P xs)
    → All Q (pass p)
    → All Q (fail p)
    → All Q xs
  disjunct-elim p ∀Qpass ∀Qfail with pass p | fail p | pass-passes p | fail-fails p | pass-is-sublist p | fail-is-sublist p | conservation p

  disjunct-elim _ _ _ | _ | _ | _ | _ | [] | [] | _ = []

  disjunct-elim {xs = x ∷ xs and x∉xs} p ∀Qpass (Qx ∷ ∀Qfail) | pass[p] | x ∷ fail[p] and x∉fail[p] | ∀Ppass[p] | _ ∷ ∀¬Pfail[p] | x ∺ pass[p]≼xs | x ∷ fail[p]≼xs | _ ∷ conservation[p] = Qx ∷ disjunct-elim p′ ∀Qpass ∀Qfail where
    p′ : Partition P xs
    pass            p′ = pass[p]
    fail            p′ = fail[p]
    pass-passes     p′ = ∀Ppass[p]
    fail-fails      p′ = ∀¬Pfail[p]
    pass-is-sublist p′ = pass[p]≼xs
    fail-is-sublist p′ = fail[p]≼xs
    conservation    p′ = UListAll.map-∈ (λ y y∈xs → ⊎.rec inₗ (inᵣ ∘ aux y y∈xs)) conservation[p] where
      aux : ∀ y → y ∈ xs → y ∈ x ∷ fail[p] and x∉fail[p] → y ∈ fail[p]
      aux x x∈xs (here  refl)      = x∈xs ↯ All¬⇒¬Any x∉xs
      aux y y∈xs (there y∈fail[p]) = y∈fail[p]

  disjunct-elim {x ∷ xs and x∉xs} p (Qx ∷ ∀Qpass) ∀Qfail | x ∷ pass[p] and x∉pass[p] | fail[p] | _ ∷ ∀Ppass[p] | ∀¬Pfail[p] | x ∷ pass[p]≼xs | x ∺ fail[p]≼xs | _ ∷ conservation[p] = Qx ∷ disjunct-elim p′ ∀Qpass ∀Qfail where
    p′ : Partition P xs
    pass            p′ = pass[p]
    fail            p′ = fail[p]
    pass-passes     p′ = ∀Ppass[p]
    fail-fails      p′ = ∀¬Pfail[p]
    pass-is-sublist p′ = pass[p]≼xs
    fail-is-sublist p′ = fail[p]≼xs
    conservation    p′ = UListAll.map-∈ (λ y y∈xs → ⊎.rec (inₗ ∘ aux y y∈xs) inᵣ) conservation[p] where
      aux : ∀ y → y ∈ xs → y ∈ x ∷ pass[p] and x∉pass[p] → y ∈ pass[p]
      aux x x∈xs (here  refl)      = x∈xs ↯ All¬⇒¬Any x∉xs
      aux y y∈xs (there y∈pass[p]) = y∈pass[p]

  -- Impossible cases.
  disjunct-elim _ _ _ | _ | _ | Px ∷ _ | ¬Px ∷ _ | _ ∷ _ | _ ∷ _ | _ = Px ↯ ¬Px
  disjunct-elim {xs = _ ∷ _ and x∉xs} _ _ _ | _ | _ | _ | _ | _ ∺ pass≼xs | _ ∺ _ | inₗ x∈pass ∷ _ = x∈pass ↯ All¬⇒¬Any (≼-preserves-∉ pass≼xs x∉xs)
  disjunct-elim {xs = _ ∷ _ and x∉xs} _ _ _ | _ | _ | _ | _ | _ ∺ _ | x ∺ fail≼xs | inᵣ x∈fail ∷ _ = x∈fail ↯ All¬⇒¬Any (≼-preserves-∉ fail≼xs x∉xs)
