module Base.List.Any where

open import Base.Level
open import Base.Type
open import Base.Type.Negation
open import Base.Pi
open import Base.Sigma
  hiding ( ind
         ; rec
         )
open import Base.Product
  as ×
  hiding ( ind
         ; rec
         )
open import Base.Equality
  hiding ( ind
         ; rec
         )
open import Base.Decide
  as Decide
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
  using ( Any
        ; here
        ; there
        ; _∈_
        )

ind :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
  → (P : ∀ xs → Any B xs → Type ℓ₃)
  → (∀ x xs Bx             → P (x ∷ xs) (here Bx))
  → (∀ x xs Bxs → P xs Bxs → P (x ∷ xs) (there Bxs))
  → ∀ xs → Π (Any B xs) (P xs)
ind P h t _ (here  Bx  ) = h _ _ Bx
ind P h t _ (there ∃xsB) = t _ _ ∃xsB (ind P h t _ ∃xsB)

rec :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {B : A → Type ℓ₂}
  → {P : List A → Type ℓ₃}
  → (∀ x xs → B x             → P (x ∷ xs))
  → (∀ x xs → Any B xs → P xs → P (x ∷ xs))
  → ∀ xs → (Any B xs → P xs)
rec = ind _

map :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
  → (∀ x → P x → Q x)
  → {xs : List A}
  → Any P xs
  → Any Q xs
map f (here  Px)   = here  (f _ Px)
map f (there ∃xsP) = there (map f ∃xsP)

map-∈ :
  ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Type ℓ₁} {P : A → Type ℓ₂} {Q : A → Type ℓ₃}
    {xs : List A}
  → (∀ x → x ∈ xs → P x → Q x)
  → Any P xs
  → Any Q xs
map-∈ f (here  Px)   = here  (f _ (here refl) Px)
map-∈ f (there ∃xsP) = there (map-∈ (λ x → f x ∘ there) ∃xsP)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  head : ∀ {x xs} → ¬ Any P xs → Any P (x ∷ xs) → P x
  head ¬∃xsP (here  Px  ) = Px
  head ¬∃xsP (there ∃xsP) = ∃xsP ↯ ¬∃xsP

  tail : ∀ {x xs} → ¬ P x → Any P (x ∷ xs) → Any P xs
  tail ¬Px (here  Px  ) = Px ↯ ¬Px
  tail ¬Px (there ∃Pxs) = ∃Pxs

  remove : {xs : List A} → Any P xs → List A × Σ[ x ] P x
  remove {x ∷ xs} (here  Px  ) = xs , (x , Px)
  remove {x ∷ xs} (there ∃xsP) = ×.lmap (x ∷_) (remove ∃xsP)

  modify : (∀ x → P x → A) → {xs : List A} → Any P xs → List A
  modify f {x ∷ xs} (here  Px  ) = f x Px ∷ xs
  modify f {x ∷ xs} (there ∃xsP) = x ∷ modify f ∃xsP

  modify-∈ : {xs : List A} → (∀ x → x ∈ xs → P x → A) → Any P xs → List A
  modify-∈ {x ∷ xs} f (here  Px  ) = f x (here refl) Px ∷ xs
  modify-∈ {x ∷ xs} f (there ∃xsP) = x ∷ modify-∈ (λ x x∈xs Px → f x (there x∈xs) Px) ∃xsP

map-compat :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Type ℓ₁} {P : A → Type ℓ₂}
    {B : Type ℓ₃} {Q : B → Type ℓ₄}
    {f : A → B}
  → (∀ x → P x → Q (f x))
  → {xs : List A}
  → Any P xs
  → Any Q (List.map f xs)
map-compat ϕ (here  Px  ) = here  (ϕ _ Px)
map-compat ϕ (there ∃xsP) = there (map-compat ϕ ∃xsP)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} where

  Decide:Any :
      {P : A → Type ℓ₂}
    → ⦃ _ : ∀ {x} → Decide (P x) ⦄ →
    ∀ {xs} → Decide (Any P xs)
  Decide:Any {P} {[]} = no λ()
  Decide:Any {P} {x ∷ xs} with decide (P x)
  ... | yes Px  = yes (here Px)
  ... | no  ¬Px = Decide.bimap there (tail ¬Px) (Decide:Any {P} {xs})
