module Finite.UList.Core where

--------------------------------------------------------------------------------
-- Lists which contain no duplicate elements.
--
-- The basic idea for this type is from "Insane descriptions"
-- (http://effectfully.blogspot.com/2016/10/insane-descriptions.html).
--------------------------------------------------------------------------------

open import Base.Level
  hiding ( zero
         ; succ
         )
open import Base.Type
open import Base.Type.Negation
open import Base.Pi
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality
open import Base.Decide
  hiding ( map
         )
open import Base.Nat
  using ( ℕ
        ; zero
        ; succ
        )

infix 4 _∉_ _∈_

data UList {ℓ} (A : Type ℓ) : Type ℓ
data All {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : UList A → Type (ℓ₁ ⊔ ℓ₂)
_∉_ : ∀ {ℓ} {A : Type ℓ} → A → UList A → Type ℓ
_∉_ x = All (_≢ x)

data UList A where
  [] : UList A
  _∷_and_ : ∀ x xs → x ∉ xs → UList A

data All P where
  [] : All P []
  _∷_ : ∀ {x xs x∉xs} → P x → All P xs → All P (x ∷ xs and x∉xs)

data Any {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : UList A → Type (ℓ₁ ⊔ ℓ₂) where
  here  : ∀ {x xs x∉xs} → P x      → Any P (x ∷ xs and x∉xs)
  there : ∀ {x xs x∉xs} → Any P xs → Any P (x ∷ xs and x∉xs)

_∈_ : ∀ {ℓ} {A : Type ℓ} → A → UList A → Type ℓ
x ∈ xs = Any (_≡ x) xs

fold : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B → B) → B → UList A → B
fold _·_ e []             = e
fold _·_ e (x ∷ xs and _) = x · fold _·_ e xs

length : ∀ {ℓ} {A : Type ℓ} → UList A → ℕ
length = fold (const succ) zero

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} where

  map : (f : A → B) → Injective f → UList A → UList B
  map-∉ : (f : A → B) (inj : Injective f) {x : A} {xs : UList A} → x ∉ xs → f x ∉ map f inj xs

  map f inj []                = []
  map f inj (x ∷ xs and x∉xs) = f x ∷ map f inj xs and map-∉ f inj x∉xs

  map-∉ f inj {x} []           = []
  map-∉ f inj {x} (y≢x ∷ x∉xs) = contramap inj y≢x ∷ map-∉ f inj x∉xs

  length-map : (f : A → B) (inj : Injective f) (xs : UList A) → length (map f inj xs) ≡ length xs
  length-map f inj []             = refl
  length-map f inj (x ∷ xs and _) = cong succ (length-map f inj xs)

  ∈-map : (f : A → B) (inj : Injective f) {x : A} {xs : UList A} → x ∈ xs → f x ∈ map f inj xs
  ∈-map f inj (here  refl) = here refl
  ∈-map f inj (there x∈xs) = there (∈-map f inj x∈xs)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  -- De Morgan dual operators. The hypothetical term which would be named
  -- ¬All⇒Any¬ cannot be constructed (it would require LEM).

  Any⇒¬All¬ : ∀ {xs : UList A} → Any P xs → ¬ All (¬_ ∘ P) xs
  Any⇒¬All¬ (here  Px)    (¬Px ∷ ¬∀¬Pxs) = Px ⊥ ¬Px
  Any⇒¬All¬ (there ∃Pxs)  (¬Px ∷ ¬∀¬Pxs) = Any⇒¬All¬ ∃Pxs ¬∀¬Pxs

  All¬⇒¬Any : ∀ {xs : UList A} → All (¬_ ∘ P) xs → ¬ Any P xs
  All¬⇒¬Any = flip Any⇒¬All¬

  ¬Any⇒All¬ : ∀ {xs : UList A} → ¬ Any P xs → All (¬_ ∘ P) xs
  ¬Any⇒All¬ {[]}              ¬∃P[]   = []
  ¬Any⇒All¬ {x ∷ xs and x∉xs} ¬∃Px∷xs = ¬Px ∷ ¬Any⇒All¬ ¬∃Pxs where
    ¬Px : ¬ P x
    ¬Px = contramap here ¬∃Px∷xs
    ¬∃Pxs : ¬ Any P xs
    ¬∃Pxs = contramap there ¬∃Px∷xs

module _ {ℓ} {A : Type ℓ} where

  ∈⇒¬∉ : {x : A} {xs : UList A} → x ∈ xs → ¬ (x ∉ xs)
  ∈⇒¬∉ = Any⇒¬All¬

  ∉⇒¬∈ : {x : A} {xs : UList A} → x ∉ xs → ¬ (x ∈ xs)
  ∉⇒¬∈ = All¬⇒¬Any

  ¬∈⇒∉ : {x : A} {xs : UList A} → ¬ (x ∈ xs) → x ∉ xs
  ¬∈⇒∉ = ¬Any⇒All¬
