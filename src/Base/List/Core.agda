module Base.List.Core where

open import Base.Level
  hiding ( succ
         ; zero
         )
open import Base.Type
open import Base.Pi
open import Base.Equality
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

infixr 5 _++_

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

foldr : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B → B) → B → List A → B
foldr _·_ e []       = e
foldr _·_ e (x ∷ xs) = x · foldr _·_ e xs
{-# COMPILE GHC foldr = \ _ _ _ _ -> foldr #-}

map : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
{-# COMPILE GHC map = \ _ _ _ _ -> map #-}

_++_ : ∀ {ℓ} {A : Type ℓ} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
{-# COMPILE GHC _++_ = \ _ _ -> (++) #-}

length : ∀ {ℓ} {A : Type ℓ} → List A → ℕ
length = foldr (const succ) zero

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

abstract

  private
    ∷≡-intro :
      ∀ {ℓ}
        {A : Type ℓ}
        {x y : A}
        {xs ys : List A}
      → x ≡ y
      → xs ≡ ys
      → x ∷ xs ≡ y ∷ ys
    ∷≡-intro refl refl = refl

  map-≐ :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁} {B : Type ℓ₂}
      {f g : A → B}
    → f ≐ g → map f ≐ map g
  map-≐ f≐g []       = refl
  map-≐ f≐g (x ∷ xs) = ∷≡-intro (f≐g x) (map-≐ f≐g xs)

  map-id :
    ∀ {ℓ}
      {A : Type ℓ}
    → map (id ∶ A ⟶ A) ≐ id
  map-id []       = refl
  map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

  map-∘ :
    ∀ {ℓ₁ ℓ₂ ℓ₃}
      {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
      (g : B → C) (f : A → B)
    → map (g ∘ f) ≐ (map g ∘ map f)
  map-∘ g f []       = refl
  map-∘ g f (x ∷ xs) = cong (g (f x) ∷_) (map-∘ g f xs)

  foldr-map :
    ∀ {ℓ₁ ℓ₂ ℓ₃}
      {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
      (_·_ : B → C → C)
      (e : C)
      (f : A → B)
      (xs : List A)
    → foldr _·_ e (map f xs) ≡ foldr (λ a c → f a · c) e xs
  foldr-map _·_ e f []       = refl
  foldr-map _·_ e f (x ∷ xs) = cong (f x ·_) (foldr-map _·_ e f xs)

  foldr-const-is-ℕ-foldr :
    ∀ {ℓ₁ ℓ₂}
      {A : Type ℓ₁} {B : Type ℓ₂}
      (f : B → B)
      (e : B)
      (xs : List A)
    → foldr (const f) e xs ≡ ℕ.foldr f e (length xs)
  foldr-const-is-ℕ-foldr f e []       = refl
  foldr-const-is-ℕ-foldr f e (x ∷ xs) = cong f (foldr-const-is-ℕ-foldr f e xs)
