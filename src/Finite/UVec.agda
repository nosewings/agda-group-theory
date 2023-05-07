module Finite.UVec where

open import Base.Level
  hiding ( zero
         ; succ
         )
open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Sigma
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality
open import Base.Nat
  hiding ( foldr
         )
open import Base.Fin
  as Fin

open import Finite.UList
  as UList
  using ( UList
        ; []
        ; _∷_and_
        ; _∷_
        ; here
        ; there
        )

infix 4 _∉_ _∈_

data UVec {ℓ} (A : Type ℓ) : ℕ → Type ℓ
data All {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : ∀ {n} → UVec A n → Type (ℓ₁ ⊔ ℓ₂)
_∉_ : ∀ {ℓ} {A : Type ℓ} → A → ∀ {n} → UVec A n → Type ℓ
_∉_ x = All (_≢ x)

data UVec A where
  [] : UVec A zero
  _∷_and_ : ∀ x {n} (xs : UVec A n) → x ∉ xs → UVec A (succ n)

data All {ℓ₁} {ℓ₂} {A} P where
  [] : All P []
  _∷_ : ∀ {x n} {xs : UVec A n} {x∉xs} → P x → All P xs → All P (x ∷ xs and x∉xs)

data Any {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : ∀ {n} → UVec A n → Type (ℓ₁ ⊔ ℓ₂) where
  here  : ∀ {x} {n} {xs : UVec A n} {x∉xs} → P x      → Any P (x ∷ xs and x∉xs)
  there : ∀ {x} {n} {xs : UVec A n} {x∉xs} → Any P xs → Any P (x ∷ xs and x∉xs)

_∈_ : ∀ {ℓ} {A : Type ℓ} → A → ∀ {n} → UVec A n → Type ℓ
x ∈ xs = Any (_≡ x) xs

foldr : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B → B) → B → ∀ {n} → UVec A n → B
foldr _·_ e []             = e
foldr _·_ e (x ∷ xs and _) = x · foldr _·_ e xs

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  Any⇒¬All¬ : ∀ {n} {xs : UVec A n} → Any P xs → ¬ All (¬_ ∘ P) xs
  Any⇒¬All¬ (here  Px)    (¬Px ∷ ¬∀¬Pxs) = Px ⊥ ¬Px
  Any⇒¬All¬ (there ∃Pxs)  (¬Px ∷ ¬∀¬Pxs) = Any⇒¬All¬ ∃Pxs ¬∀¬Pxs

  All¬⇒¬Any : ∀ {n} {xs : UVec A n} → All (¬_ ∘ P) xs → ¬ Any P xs
  All¬⇒¬Any = flip Any⇒¬All¬

  ¬Any⇒All¬ : ∀ {n} {xs : UVec A n} → ¬ Any P xs → All (¬_ ∘ P) xs
  ¬Any⇒All¬ {xs = []}              ¬∃P[]   = []
  ¬Any⇒All¬ {xs = x ∷ xs and x∉xs} ¬∃Px∷xs = ¬Px ∷ ¬Any⇒All¬ ¬∃Pxs where
    ¬Px : ¬ P x
    ¬Px = ¬.contramap here ¬∃Px∷xs
    ¬∃Pxs : ¬ Any P xs
    ¬∃Pxs = ¬.contramap there ¬∃Px∷xs

module _ {ℓ} {A : Type ℓ} where

  ∈⇒¬∉ : ∀ {x : A} {n} {xs : UVec A n} → x ∈ xs → ¬ (x ∉ xs)
  ∈⇒¬∉ = Any⇒¬All¬

  ∉⇒¬∈ : ∀ {x : A} {n} {xs : UVec A n} → x ∉ xs → ¬ (x ∈ xs)
  ∉⇒¬∈ = All¬⇒¬Any

  ¬∈⇒∉ : ∀ {x : A} {n} {xs : UVec A n} → ¬ (x ∈ xs) → x ∉ xs
  ¬∈⇒∉ = ¬Any⇒All¬

module _ {ℓ} {A : Type ℓ} where

  length : ∀ {n} → UVec A n → ℕ
  length = foldr (const succ) zero

  index : ∀ {n} → UVec A n → Fin n → A
  index (x ∷ xs and _) zero     = x
  index (x ∷ xs and _) (succ i) = index xs i

  index⇒∈ : ∀ {x} {n} (xs : UVec A n) i → index xs i ≡ x → x ∈ xs
  index⇒∈ (x ∷ xs and _) zero     = λ{ refl → here refl }
  index⇒∈ (_ ∷ xs and _) (succ i) = there ∘ index⇒∈ xs i

  ∈⇒index : ∀ {x} {n} {xs : UVec A n} → x ∈ xs → Σ[ i ] index xs i ≡ x
  ∈⇒index (here  refl) = zero , refl
  ∈⇒index (there x∈xs) = let (i , xs[i]≡x) = ∈⇒index x∈xs in succ i , xs[i]≡x

  index-inj : ∀ {n} (xs : UVec A n) → Injective (index xs)
  index-inj xs                {zero  } {zero  } = λ _       → refl
  index-inj (x ∷ xs and x∉xs) {zero  } {succ j} = λ x≡xs[j] → index⇒∈ xs j (sym x≡xs[j]) ↯ ∉⇒¬∈ x∉xs
  index-inj (x ∷ xs and x∉xs) {succ i} {zero  } = λ xs[i]≡i → index⇒∈ xs i xs[i]≡i       ↯ ∉⇒¬∈ x∉xs
  index-inj (x ∷ xs and _   ) {succ i} {succ j} = cong succ ∘ index-inj xs

  from-UList : (xs : UList A) → UVec A (UList.length xs)
  from-UList-∉ : {x : A} {xs : UList A} → x UList.∉ xs → x ∉ from-UList xs

  from-UList []                = []
  from-UList (x ∷ xs and x∉xs) = x ∷ from-UList xs and from-UList-∉ x∉xs

  from-UList-∉ []           = []
  from-UList-∉ (y≢x ∷ x∉xs) = y≢x ∷ from-UList-∉ x∉xs

  from-UList-∈ : ∀ {x xs} → x UList.∈ xs → x ∈ from-UList xs
  from-UList-∈ (here  refl) = here  refl
  from-UList-∈ (there x∈xs) = there (from-UList-∈ x∈xs)

  to-UList : ∀ {n} → UVec A n → UList A
  to-UList-∉ : ∀ {x : A} {n} {xs : UVec A n} → x ∉ xs → x UList.∉ (to-UList xs)

  to-UList []                = []
  to-UList (x ∷ xs and x∉xs) = x ∷ to-UList xs and to-UList-∉ x∉xs

  to-UList-∉ []           = []
  to-UList-∉ (y≢x ∷ x∉xs) = y≢x ∷ to-UList-∉ x∉xs

  to-UList-∈ : ∀ {x n} {xs : UVec A n} → x ∈ xs → x UList.∈ to-UList xs
  to-UList-∈ (here  refl) = here  refl
  to-UList-∈ (there x∈xs) = there (to-UList-∈ x∈xs)

  abstract
    to-UList-length : ∀ {n} (xs : UVec A n) → UList.length (to-UList xs) ≡ n
    to-UList-length []             = refl
    to-UList-length (x ∷ xs and _) = cong succ (to-UList-length xs)

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} where

  map : (f : A → B) → Injective f → ∀ {n} → UVec A n → UVec B n
  map-∉ : ∀ (f : A → B) (inj : Injective f) {x n} {xs : UVec A n} → x ∉ xs → f x ∉ map f inj xs
  
  map f inj []                = []
  map f inj (x ∷ xs and x∉xs) = f x ∷ map f inj xs and map-∉ f inj x∉xs

  map-∉ f inj []           = []
  map-∉ f inj (y≢x ∷ x∉xs) = ¬.contramap inj y≢x ∷ map-∉ f inj x∉xs

  map-∈ : ∀ (f : A → B) (inj : Injective f) {x n} {xs : UVec A n} → x ∈ xs → f x ∈ map f inj xs
  map-∈ f inj (here  refl) = here refl
  map-∈ f inj (there x∈xs) = there (map-∈ f inj x∈xs)

fins : (n : ℕ) → UVec (Fin n) n
fins-∉ : {m n : ℕ} (xs : UVec (Fin n) m) → zero ∉ map succ Fin.succ-inj xs

fins zero     = []
fins (succ n) = zero ∷ map succ Fin.succ-inj (fins n) and fins-∉ (fins n)

fins-∉ []             = []
fins-∉ (x ∷ xs and _) = succ≢zero _ ∷ fins-∉ xs

fins-∈ : ∀ {n} (i : Fin n) → i ∈ fins n
fins-∈ {succ n} zero     = here refl
fins-∈ {succ n} (succ i) = there (map-∈ _ _ (fins-∈ i))

record Enumeration {ℓ} {A : Type ℓ} {n} (xs : UVec A n) : Type ℓ where
  constructor intro
  field
    locate : ∀ x → x ∈ xs

record Size {ℓ} (A : Type ℓ) (n : ℕ) : Type ℓ where
  constructor intro
  field
    elements : UVec A n
    ⦃ enumeration ⦄ : Enumeration elements
open Size ⦃...⦄
  public

record Finite {ℓ} (A : Type ℓ) : Type ℓ where
  constructor intro
  field
    size : ℕ
    ⦃ has-size ⦄ : Size A size
open Finite ⦃...⦄
  public

instance
  Enumeration:fins : ∀ {n} → Enumeration (fins n)
  Enumeration:fins = intro fins-∈
