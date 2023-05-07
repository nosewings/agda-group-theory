module Base.List.Any where

open import Base.Level
open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Equality
open import Base.Decide
  as Decide
  hiding ( map
         )
open import Base.List.Core

data Any {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : List A → Type (ℓ₁ ⊔ ℓ₂) where
  here  : ∀ {x xs} → P x      → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

_∈_ : ∀ {ℓ} {A : Type ℓ} → A → List A → Type ℓ
_∈_ x = Any (_≡ x)

module _ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃} where

  hmap : (∀ {x} → P x → Q x) → {xs : List A} → Any P xs → Any Q xs
  hmap f (here  Px  ) = here  (f Px)
  hmap f (there ∃xsP) = there (hmap f ∃xsP)

  hmap-∈ : ∀ {xs} → (∀ {x} → x ∈ xs → P x → Q x) → Any P xs → Any Q xs
  hmap-∈ f (here  Px  ) = here  (f (here refl) Px)
  hmap-∈ f (there ∃xsP) = there (hmap-∈ (f ∘ there) ∃xsP)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  head : ∀ {x xs} → ¬ Any P xs → Any P (x ∷ xs) → P x
  head ¬∃xsP (here  Px  ) = Px
  head ¬∃xsP (there ∃xsP) = ∃xsP ↯ ¬∃xsP

  tail : ∀ {x xs} → ¬ P x → Any P (x ∷ xs) → Any P xs
  tail ¬Px (here  Px  ) = Px ↯ ¬Px
  tail ¬Px (there ∃Pxs) = ∃Pxs

  modify : (∀ x → P x → A) → {xs : List A} → Any P xs → List A
  modify f {x ∷ xs} (here  Px  ) = f x Px ∷ xs
  modify f {x ∷ xs} (there ∃xsP) = x ∷ modify f ∃xsP

  modify-∈ : {xs : List A} → (∀ x → x ∈ xs → P x → A) → Any P xs → List A
  modify-∈ {x ∷ xs} f (here  Px  ) = f x (here refl) Px ∷ xs
  modify-∈ {x ∷ xs} f (there ∃xsP) = x ∷ modify-∈ (λ x x∈xs Px → f x (there x∈xs) Px) ∃xsP

map-over-map :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Type ℓ₁} {P : A → Type ℓ₂}
    {B : Type ℓ₃} {Q : B → Type ℓ₄}
    {f : A → B}
  → (∀ {x} → P x → Q (f x))
  → {xs : List A}
  → Any P xs
  → Any Q (map f xs)
map-over-map ϕ (here  Px  ) = here  (ϕ Px)
map-over-map ϕ (there ∃xsP) = there (map-over-map ϕ ∃xsP)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  any? : (∀ x → Decide (P x)) → ∀ xs → Decide (Any P xs)
  any? ϕ []       = no (λ ())
  any? ϕ (x ∷ xs) with ϕ x
  ... | yes  Px = yes (here Px)
  ... | no  ¬Px = Decide.map there (tail ¬Px) (any? ϕ xs)

  instance
    Decide:Any : ⦃ _ : ∀ {x} → Decide (P x) ⦄ → ∀ {xs} → Decide (Any P xs)
    Decide:Any ⦃ dec ⦄ = any? (λ _ → dec) _
