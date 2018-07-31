module Base.List.Core where

open import Base.Level
  hiding ( succ
         ; zero
         )
open import Base.Type
open import Base.Type.Negation
open import Base.Pi
open import Base.Product
  hiding ( ind
         ; rec
         )
open import Base.Maybe
  hiding ( ind
         ; rec
         ; map
         ; Any
         )
open import Base.Equality
  hiding ( ind
         ; rec
         )
open import Base.Decide
  hiding ( ind
         ; rec
         )
open import Base.Nat
  as ℕ
  using ( ℕ
        ; succ
        ; zero
        ; _+_
        ; _*_
        )

infix 4 _∈_ _∈!_

open import Agda.Builtin.List
  public

ind :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    (P : List A → Type ℓ₂)
  → P []
  → (∀ x xs → P xs → P (x ∷ xs))
  → Π (List A) P
ind P n c []       = n
ind P n c (x ∷ xs) = c x xs (ind P n c xs)

rec :
  ∀ {ℓ₁ ℓ₂}
    {A : Type ℓ₁}
    {P : Type ℓ₂}
  → P
  → (A → List A → P → P)
  → (List A → P)
rec = ind _

map : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

fold : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B → B) → B → List A → B
fold _·_ e []       = e
fold _·_ e (x ∷ xs) = x · fold _·_ e xs

replicate : ∀ {ℓ} {A : Type ℓ} → ℕ → A → List A
replicate n x = ℕ.fold (x ∷_) [] n

module _ {ℓ} {A : Type ℓ} where

  infixr 5 _++_

  length : List A → ℕ
  length = fold (const succ) zero

  _++_ : List A → List A → List A
  xs ++ ys = fold _∷_ ys xs

sum : List ℕ → ℕ
sum = fold _+_ 0

product : List ℕ → ℕ
product = fold _*_ 1

concat-maybes : ∀ {ℓ} {A : Type ℓ} → List (Maybe A) → List A
concat-maybes {A = A} = fold f [] where
  f : Maybe A → List A → List A
  f none     xs = xs
  f (just x) xs = x ∷ xs

abstract

  map-∘ :
    ∀ {ℓ₁ ℓ₂ ℓ₃}
      {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
      (g : B → C) (f : A → B)
      (xs : List A)
    → map (g ∘ f) xs ≡ (map g ∘ map f) xs
  map-∘ g f []       = refl
  map-∘ g f (x ∷ xs) = cong (g (f x) ∷_) (map-∘ g f xs)

  map-≐ :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁} {B : Type ℓ₂}
      {f g : A → B}
    → f ≐ g → (xs : List A) → map f xs ≡ map g xs
  map-≐ f≐g [] = refl
  map-≐ f≐g (x ∷ xs) rewrite f≐g x | map-≐ f≐g xs = refl

  map-const-replicate :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁} {B : Type ℓ₂}
      (y : B)
      (xs : List A)
    → map (const y) xs ≡ replicate (length xs) y
  map-const-replicate y []       = refl
  map-const-replicate y (x ∷ xs) = cong (y ∷_) (map-const-replicate y xs)

  fold-map :
    ∀ {ℓ₁ ℓ₂ ℓ₃}
      {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
      (f : A → B)
      (_·_ : B → C → C)
      (e : C)
      (xs : List A)
    → fold _·_ e (map f xs) ≡ fold (λ a c → f a · c) e xs
  fold-map f _·_ e []       = refl
  fold-map f _·_ e (x ∷ xs) = cong (f x ·_) (fold-map f _·_ e xs)

  fold-ℕ-fold :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁} {B : Type ℓ₂}
      (f : B → B)
      (e : B)
      (xs : List A)
    → fold (λ _ x → f x) e xs ≡ ℕ.fold f e (length xs)
  fold-ℕ-fold f e []       = refl
  fold-ℕ-fold f e (x ∷ xs) = cong f (fold-ℕ-fold f e xs)

data All {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : List A → Type (ℓ₁ ⊔ ℓ₂) where
  [] : All P []
  _∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

data Any {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : List A → Type (ℓ₁ ⊔ ℓ₂) where
  here  : ∀ {x xs} → P x      → Any P (x ∷ xs)
  there : ∀ {x xs} → Any P xs → Any P (x ∷ xs)

_∈_ : ∀ {ℓ} {A : Type ℓ} → A → List A → Type ℓ
_∈_ x = Any (_≡ x)

data One {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : List A → Type (ℓ₁ ⊔ ℓ₂) where
  here    : ∀ {x xs} → P x → All (¬_ ∘ P) xs → One P (x ∷ xs)
  nothere : ∀ {x xs} → ¬ P x → One P xs → One P (x ∷ xs)

_∈!_ : ∀ {ℓ} {A : Type ℓ} → A → List A → Type ℓ
_∈!_ x = One (_≡ x)
