module Base.List.All where

open import Base.Level
open import Base.Type
open import Base.Pi
open import Base.Equality
  hiding ( ind
         ; rec
         )

open import Base.List.Core
  as List
  hiding ( ind
         ; rec
         ; map
         )

open import Base.List.Core
  public
  using ( All
        ; []
        ; _∷_
        )

ind :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    (P : ∀ xs → All B xs → Type ℓ₃)
  → P [] []
  → (∀ x xs Bx Bxs → P xs Bxs → P (x ∷ xs) (Bx ∷ Bxs))
  → ∀ xs → Π (All B xs) (P xs)
ind P n c _ []        = n
ind P n c _ (Bx ∷ Bs) = c _ _ Bx Bs (ind P n c _ Bs)

rec :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
    {P : List A → Type ℓ₃}
  → P []
  → (∀ x xs → B x → All B xs → P xs → P (x ∷ xs))
  → ∀ xs → (All B xs → P xs)
rec = ind _

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  head : {x : A} {xs : List A} → All P (x ∷ xs) → P x
  head (Px ∷ _) = Px

  tail : {x : A} {xs : List A} → All P (x ∷ xs) → All P xs
  tail (_ ∷ ∀xsP) = ∀xsP

  apply : {xs : List A} → All P xs → {x : A} → x ∈ xs → P x
  apply (Px ∷ Pxs) (here  refl) = Px
  apply (Py ∷ Pxs) (there x∈xs) = apply Pxs x∈xs

map :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
  → (∀ x → P x → Q x) →
  ∀ {xs} → All P xs → All Q xs
map f []         = []
map f (Px ∷ Pxs) = f _ Px ∷ map f Pxs

map-compat :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : Type ℓ₂} {P : B → Type ℓ₃}
    {f : A → B}
    {xs : List A}
  → (∀ x → P (f x))
  → All P (List.map f xs)
map-compat {xs = []}     ϕ = []
map-compat {xs = x ∷ xs} ϕ = ϕ x ∷ map-compat ϕ 

map-over :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Type ℓ₁} {B : Type ℓ₂} {P : A → Type ℓ₃} {Q : B → Type ℓ₄}
    {f : A → B}
  → (∀ x → P x → Q (f x))
  → {xs : List A}
  → All P xs → All Q (List.map f xs)
map-over P⇒Qf []          = []
map-over P⇒Qf (Px ∷ ∀xsP) = P⇒Qf _ Px ∷ map-over P⇒Qf ∀xsP

≡[]-inv :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁} {P : A → Type ℓ₂}
    (ϕ : All P [])
  → ϕ ≡ []
≡[]-inv [] = refl
