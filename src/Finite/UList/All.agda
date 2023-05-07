module Finite.UList.All where

open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Sigma
open import Base.Equality
open import Base.IsProp
open import Base.Nat

open import Finite.UList.Core
  hiding ( map
         )

open import Finite.UList.Core
  public
  using ( All
        ; []
        ; _∷_
        ; _∉_
        )

head :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {P : A → Type ℓ₂}
    {x : A} {xs : UList A} {x∉xs}
  → All P (x ∷ xs and x∉xs)
  → P x
head (Px ∷ ∀Pxs) = Px

tail :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {P : A → Type ℓ₂}
    {x : A} {xs : UList A} {x∉xs}
  → All P (x ∷ xs and x∉xs)
  → All P xs
tail (Px ∷ ∀Pxs) = ∀Pxs

from-Π-∈ :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {P : A → Type ℓ₂}
    {xs : UList A}
  → (∀ x → x ∈ xs → P x)
  → All P xs
from-Π-∈ {xs = []}              f = []
from-Π-∈ {xs = x ∷ xs and x∈xs} f = f x (here refl) ∷ from-Π-∈ (λ x → f x ∘ there)

map :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
  → (∀ x → P x → Q x)
  → {xs : UList A}
  → All P xs
  → All Q xs
map f []         = []
map f (Px ∷ ∀Pxs) = f _ Px ∷ map f ∀Pxs

map-∈ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
    {xs : UList A}
  → (∀ x → x ∈ xs → P x → Q x)
  → All P xs
  → All Q xs
map-∈ f []          = []
map-∈ f (Px ∷ ∀Pxs) = f _ (here refl) Px ∷ map-∈ (λ x x∈xs Px → f x (there x∈xs) Px) ∀Pxs

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  apply :
      {xs : UList A}
    → All P xs
    → {x : A} → x ∈ xs → P x
  apply (Px ∷ ∀xsP) (here refl)  = Px
  apply (Py ∷ ∀xsP) (there x∈xs) = apply ∀xsP x∈xs

  to-UList :
      {xs : UList A}
    → All P xs
    → UList (Σ A P)
  to-UList-∉ :
      {xs : UList A}
      (∀xsP : All P xs)
      {x : A}
    → x ∉ xs
    → (Px : P x)
    → (x , Px) ∉ to-UList ∀xsP

  to-UList                       []          = []
  to-UList {xs = _ ∷ _ and x∉xs} (Px ∷ ∀xsP) = (_ , Px) ∷ to-UList ∀xsP and to-UList-∉ ∀xsP x∉xs Px

  to-UList-∉ []          []           Px = []
  to-UList-∉ (Py ∷ ∀xsP) (y≢x ∷ x∉xs) Px = ¬.contramap (proj₁ ∘ Σ≡-elim _ _) y≢x ∷ to-UList-∉ ∀xsP x∉xs Px

  to-UList-length : {xs : UList A} (∀xsP : All P xs) → length (to-UList ∀xsP) ≡ length xs
  to-UList-length []          = refl
  to-UList-length (Px ∷ ∀xsP) = cong succ (to-UList-length ∀xsP)

  to-UList-prop-lookup :
      ⦃ _ : ∀ {x} → IsProp (P x) ⦄
      {xs : UList A}
      (∀xsP : All P xs)
      {x : A} → x ∈ xs
    → (Px : P x)
    → (x , Px) ∈ to-UList ∀xsP
  to-UList-prop-lookup (_ ∷ ∀xsP) (here  refl) Px = here  (Σ≡-intro _ _ (refl , prop _ _))
  to-UList-prop-lookup (_ ∷ ∀xsP) (there x∈xs) Px = there (to-UList-prop-lookup ∀xsP x∈xs Px)
