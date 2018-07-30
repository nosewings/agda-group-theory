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
open import Base.Nat

open import Finite.UList.Core
open import Finite.UList.Sublist

open import Finite.UList.Core
  public
  using ( Any
        ; here
        ; there
        ; _∈_
        )

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  tail : {x : A} {xs : UList A} {x∉xs : x ∉ xs} → Any P (x ∷ xs and x∉xs) → ¬ P x → Any P xs
  tail (here  Px  ) ¬Px = Px ↯ ¬Px
  tail (there ∃xsP) ¬Px = ∃xsP

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
  delete-∈ (here  refl) a∈xs         a≢x = tail a∈xs (sym a≢x)
  delete-∈ (there x∈xs) (here  refl) a≢x = here refl
  delete-∈ (there x∈xs) (there a∈xs) a≢x = there (delete-∈ x∈xs a∈xs a≢x)

  delete-≼ : ∀ {a xs} (a∈xs : a ∈ xs) → delete a∈xs ≼ xs
  delete-≼ {a} (here  refl) = a ∺ Base.Relation.refl
  delete-≼ {a} (there x∈xs) = _ ∷ delete-≼ x∈xs

map-∈ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
    {xs : UList A}
  → (∀ x → x ∈ xs → P x → Q x)
  → Any P xs → Any Q xs
map-∈ f (here  Px  ) = here  (f _ (here refl) Px)
map-∈ f (there ∃xsP) = there (map-∈ (λ x → f x ∘ there) ∃xsP)

instance
  Decide:Any :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁}
      {P : A → Type ℓ₂} ⦃ _ : ∀ {x} → Decide (P x) ⦄
      {xs : UList A}
    → Decide (Any P xs)
  Decide:Any {P = P} {xs = []} = no (λ ())
  Decide:Any {P = P} {xs = x ∷ xs and x∉xs} with decide (P x)
  ... | yes Px = yes (here Px)
  ... | no  ¬Px with Decide:Any {P = P} {xs = xs}
  ... | yes ∃xsP = yes (there ∃xsP)
  ... | no  ∄xsP = no  (⊎.rec ¬Px ∄xsP ∘ to-⊎)
