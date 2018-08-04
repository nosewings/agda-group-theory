module Finite.UList.Permutation where

open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality
  as ≡
open import Base.Type.LogicalEquivalence
  as ↔
  hiding ( refl
         ; sym
         ; trans
         )
open import Base.Nat

open import Finite.UList
open import Finite.UList.Sublist
open import Finite.UList.Any
  as UL∃
  hiding ( tail
         )

module _ {ℓ} {A : Type ℓ} where

  infix 4 _≈_

  _≈_ : Relation ℓ (UList A)
  xs ≈ ys = ∀ a → (a ∈ xs) ↔ (a ∈ ys)

  instance

    Reflexive:≈ : Reflexive _≈_
    Reflexive:≈ = Reflexive.intro (λ _ → ↔.refl)

    Symmetric:≈ : Symmetric _≈_
    Symmetric:≈ = Symmetric.intro (λ x≈y → λ a → ↔.sym (x≈y a))

    Transitive:≈ : Transitive _≈_
    Transitive:≈ = Transitive.intro (λ x≈y y≈z → λ a → x≈y a ⟨ ↔.trans ⟩ y≈z a)

  ≈[] : ∀ {xs} → xs ≈ [] → xs ≡ []
  ≈[] {[]         } xs≈[] = refl
  ≈[] {x ∷ _ and _} xs≈[] with _↔_.to (xs≈[] x) (here refl)
  ... | ()

  []≈ : ∀ {xs} → [] ≈ xs → xs ≡ []
  []≈ = ≈[] ∘ sym

  tail : ∀ {a xs a∉xs ys a∉ys} → (a ∷ xs and a∉xs) ≈ (a ∷ ys and a∉ys) → xs ≈ ys
  tail {a} {xs} {a∉xs} {ys} {a∉ys} ϕ = λ b → _↔_.intro (f b) (g b) where

    f : ∀ b → b ∈ xs → b ∈ ys
    f b b∈xs with _↔_.to (ϕ b) (there b∈xs)
    ... | here  refl = b∈xs ↯ ∉⇒¬∈ a∉xs
    ... | there b∈ys = b∈ys

    g : ∀ b → b ∈ ys → b ∈ xs
    g b b∈ys with _↔_.from (ϕ b) (there b∈ys)
    ... | here  refl = b∈ys ↯ ∉⇒¬∈ a∉ys
    ... | there b∈xs = b∈xs

  ≈delete : ∀ {x xs x∉xs ys} → (ϕ : (x ∷ xs and x∉xs) ≈ ys) → xs ≈ delete (_↔_.to (ϕ x) (here refl))
  ≈delete {x} {xs} {x∉xs} {ys} ϕ with _↔_.to (ϕ x) (here refl)
  ≈delete {x} {xs} {x∉xs} {y ∷ ys and y∉ys} ϕ | here  refl = tail ϕ
  ≈delete {x} {xs} {x∉xs} {y ∷ ys and y∉ys} ϕ | there x∈ys = λ a → _↔_.intro (f a) (g a)  where

    f : ∀ a → a ∈ xs → a ∈ (y ∷ delete x∈ys and delete-∉ x∈ys y∉ys)
    f a a∈xs with _↔_.to (ϕ a) (there a∈xs)
    ... | here  refl = here  refl
    ... | there a∈ys = there (delete-∈ x∈ys a∈ys a≢x) where
      a≢x : a ≢ x
      a≢x = ¬.contramap (≡.rec (_∈ xs) a∈xs _) (∉⇒¬∈ x∉xs)

    g : ∀ a → a ∈ (y ∷ delete x∈ys and delete-∉ x∈ys y∉ys) → a ∈ xs
    g y (here refl) = UL∃.tail x≢y (_↔_.from (ϕ y) (here refl)) where
      x≢y : x ≢ y
      x≢y = ¬.contramap (≡.rec (_∈ ys) x∈ys _) (∉⇒¬∈ y∉ys)
    g a (there ψ) = UL∃.tail x≢a (_↔_.from (ϕ a) (there (≼-preserves-∈ (delete-≼ x∈ys) ψ))) where
      x≢a : x ≢ a
      x≢a = ¬.contramap (≡.rec (_∈ delete x∈ys) ψ _ ∘ sym) (∉⇒¬∈ (delete-∈-∉ x∈ys))

  ≈-preserves-length : ∀ {xs ys} → xs ≈ ys → length xs ≡ length ys
  ≈-preserves-length {[]} {ys} xs≈ys rewrite []≈ xs≈ys = refl
  ≈-preserves-length {x ∷ xs and x∉xs} {ys} x∷xs≈ys =
      length (x ∷ xs and x∉xs)
        ≡⟨⟩
      succ (length xs)
        ≡⟨ ≈-preserves-length (≈delete x∷xs≈ys) |in-context succ ⟩
      succ (length (delete (_↔_.to (x∷xs≈ys x) (here refl))))
        ≡⟨ delete-length (_↔_.to (x∷xs≈ys x) (here refl)) ⟩⁻¹
      length ys
        ∎
    where open ≡Reasoning

  enumerations-are-permutations :
      (xs : UList A) (ϕ : Enumeration xs)
      (ys : UList A) (ψ : Enumeration ys)
    → xs ≈ ys
  enumerations-are-permutations xs ϕ ys ψ = λ a → _↔_.intro (λ _ → Enumeration.locate ψ a) (λ _ → Enumeration.locate ϕ a)
