module Base.List.All where

open import Base.Level
open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Equality
  hiding ( ind
         ; rec
         )
open import Base.Decide
  as Decide
  hiding ( map
         )

open import Base.List.Core
open import Base.List.Any
  hiding ( head
         ; tail
         ; hmap
         ; map-over-map
         )

data All {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : List A → Type (ℓ₁ ⊔ ℓ₂) where
  []  : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  head : {x : A} {xs : List A} → All P (x ∷ xs) → P x
  head (Px ∷ _) = Px

  tail : {x : A} {xs : List A} → All P (x ∷ xs) → All P xs
  tail (_ ∷ ∀xsP) = ∀xsP

  apply : {xs : List A} → All P xs → {x : A} → x ∈ xs → P x
  apply (Px ∷ Pxs) (here  refl) = Px
  apply (Py ∷ Pxs) (there x∈xs) = apply Pxs x∈xs

hmap :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
  → (∀ {x} → P x → Q x)
  → {xs : List A}
  → All P xs
  → All Q xs
hmap f []         = []
hmap f (Px ∷ Pxs) = f Px ∷ hmap f Pxs

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  all? : (∀ x → Decide (P x)) → ∀ xs → Decide (All P xs)
  all? ϕ []       = yes []
  all? ϕ (x ∷ xs) with ϕ x
  ... | no  ¬Px = no (¬.contramap head ¬Px)
  ... | yes  Px = Decide.map (Px ∷_) tail (all? ϕ xs)

  instance
    Decide:All : ⦃ _ : ∀ {x} → Decide (P x) ⦄ → ∀ {xs} → Decide (All P xs)
    Decide:All = all? !!! _

map-compat :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {P : B → Type ℓ₃}
    {f : A → B}
  → (∀ x → P (f x))
  → (xs : List A)
  → All P (map f xs)
map-compat ϕ []       = []
map-compat ϕ (x ∷ xs) = ϕ x ∷ map-compat ϕ xs

map-over-map :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Type ℓ₁} {B : Type ℓ₂} {P : A → Type ℓ₃} {Q : B → Type ℓ₄}
    {f : A → B}
  → (∀ {x} → P x → Q (f x))
  → {xs : List A}
  → All P xs
  → All Q (map f xs)
map-over-map ϕ []          = []
map-over-map ϕ (Px ∷ ∀xsP) = ϕ Px ∷ map-over-map ϕ ∀xsP
