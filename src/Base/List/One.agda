module Base.List.One where

open import Base.Level
open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Sigma
open import Base.Product
  hiding ( map
         )
open import Base.Equality

open import Base.List.Core
open import Base.List.All
  as All
  hiding ( map-over-map
         )

data One {ℓ₁ ℓ₂} {A : Type ℓ₁} (P : A → Type ℓ₂) : List A → Type (ℓ₁ ⊔ ℓ₂) where
  here    : ∀ {x xs} →   P x → All (¬_ ∘ P) xs → One P (x ∷ xs)
  nothere : ∀ {x xs} → ¬ P x → One P xs        → One P (x ∷ xs)

_∈!_ : ∀ {ℓ} {A : Type ℓ} → A → List A → Type ℓ
_∈!_ x = One (_≡ x)

map-over-map :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Type ℓ₁} {B : Type ℓ₂} {P : A → Type ℓ₃} {Q : B → Type ℓ₄}
    {f : A → B}
  → (∀ {x} → P x     → Q (f x))
  → (∀ {x} → Q (f x) → P x    )
  → {xs : List A}
  → One P xs → One Q (map f xs)
map-over-map ϕ ψ (here     Px  ∀xs¬P) = here    (ϕ Px)              (All.map-over-map (¬.contramap ψ) ∀xs¬P)
map-over-map ϕ ψ (nothere ¬Px  ∃!xsP) = nothere (¬.contramap ψ ¬Px) (map-over-map ϕ ψ ∃!xsP)

extract : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} {xs} → One P xs → Σ[ x ] (x ∈! xs × P x)
extract (here Px ∀xs¬P) =
      _
    , here refl (All.hmap (¬.contramap λ{ refl → Px }) ∀xs¬P)
    , Px
extract (nothere ¬Py  ∃!xsP) = let (x , x∈!xs , Px) = extract ∃!xsP in
      x
    , nothere (¬.contramap (λ{ refl → Px }) ¬Py) x∈!xs
    , Px
