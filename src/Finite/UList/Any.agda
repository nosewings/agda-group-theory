module Finite.UList.Any where

open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Sigma
open import Base.Sum
  as ⊎
open import Base.Product
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality
  as ≡
open import Base.Decide
  as Decide
open import Base.Nat

open import Finite.UList.Core
open import Finite.UList.Sublist

open import Finite.UList.Core
  public
  using ( Any
        ; here
        ; there
        ; _∈_
        ; ∈-map
        )

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  tail : {x : A} {xs : UList A} {x∉xs : x ∉ xs} → ¬ P x → Any P (x ∷ xs and x∉xs) → Any P xs
  tail ¬Px (here  Px  ) = Px ↯ ¬Px
  tail ¬Px (there ∃xsP) = ∃xsP

  extract : ∀ {xs : UList A} → Any P xs → Σ[ x ] (x ∈ xs × P x)
  extract (here  Px  ) = _ , here refl , Px
  extract (there ∃xsP) = let x , x∈xs , Px = extract ∃xsP
                         in x , there x∈xs , Px

  compress : ∀ {xs : UList A} → Σ[ x ] (x ∈ xs × P x) → Any P xs
  compress (x , here  refl , Px) = here Px
  compress (x , there x∈xs , Px) = there (compress (x , x∈xs , Px))

  to-⊎ : ∀ {x} {xs : UList A} {x∉xs} → Any P (x ∷ xs and x∉xs) → P x ⊎ Any P xs
  to-⊎ (here  Px  ) = inₗ Px
  to-⊎ (there ∃xsP) = inᵣ ∃xsP

module _ {ℓ} {A : Type ℓ} where

  ∈-length : {a : A} {xs : UList A} → a ∈ xs → length xs ≥ 1
  ∈-length (here  _) = succ zero
  ∈-length (there _) = succ zero

  delete : {a : A} {xs : UList A} → a ∈ xs → UList A
  delete-∉ : {a : A} {xs : UList A} (a∈xs : a ∈ xs) {x : A} → x ∉ xs → x ∉ delete a∈xs

  delete {xs = a ∷ xs and a∉xs} (here  refl) = xs
  delete {xs = x ∷ xs and x∉xs} (there x∈xs) = x ∷ delete x∈xs and delete-∉ x∈xs x∉xs

  delete-∉ (here  refl) (_   ∷ x∉xs) = x∉xs
  delete-∉ (there a∈xs) (y≢x ∷ x∉xs) = y≢x ∷ delete-∉ a∈xs x∉xs

  delete-∈-∉ : ∀ {a xs} (a∈xs : a ∈ xs) → a ∉ delete a∈xs
  delete-∈-∉ {a} {a ∷ xs and a∉xs} (here  refl) = a∉xs
  delete-∈-∉ {a} {x ∷ xs and x∉xs} (there a∈xs) = x≢a ∷ delete-∈-∉ a∈xs where
    x≢a : x ≢ a
    x≢a = ¬.contramap (≡.rec (_∈ xs) a∈xs _ ∘ sym) (∉⇒¬∈ x∉xs)

  delete-∈ : ∀ {x xs} (x∈xs : x ∈ xs) {a} (a∈xs : a ∈ xs) → a ≢ x → a ∈ delete x∈xs
  delete-∈ (here  refl) a∈xs         a≢x = tail (sym a≢x) a∈xs
  delete-∈ (there x∈xs) (here  refl) a≢x = here refl
  delete-∈ (there x∈xs) (there a∈xs) a≢x = there (delete-∈ x∈xs a∈xs a≢x)

  delete-≼ : ∀ {a xs} (a∈xs : a ∈ xs) → delete a∈xs ≼ xs
  delete-≼ {a} (here  refl) = a ∺ Base.Relation.refl
  delete-≼ {a} (there x∈xs) = _ ∷ delete-≼ x∈xs

  delete-length : ∀ {a xs} (a∈xs : a ∈ xs) → length xs ≡ succ (length (delete a∈xs))
  delete-length (here  refl) = refl
  delete-length (there a∈xs) = cong succ (delete-length a∈xs)

map-∈ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
    {xs : UList A}
  → (∀ x → x ∈ xs → P x → Q x)
  → Any P xs → Any Q xs
map-∈ f (here  Px  ) = here  (f _ (here refl) Px)
map-∈ f (there ∃xsP) = there (map-∈ (λ x → f x ∘ there) ∃xsP)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  any? : (∀ x → Decide (P x)) → ∀ xs → Decide (Any P xs)
  any? ϕ []       = no (λ ())
  any? ϕ (x ∷ xs and _) with ϕ x
  ... | yes  Px = yes (here Px)
  ... | no  ¬Px = Decide.map there (tail ¬Px) (any? ϕ xs)

  instance
    Decide:Any : ⦃ _ : ∀ {x} → Decide (P x) ⦄ → ∀ {xs} → Decide (Any P xs)
    Decide:Any ⦃ dec ⦄ = any? (λ _ → dec) _
