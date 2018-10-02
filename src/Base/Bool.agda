module Base.Bool where

open import Base.Type
open import Base.Pi
open import Base.Pi.Operation
open import Base.Equality
  hiding ( ind
         ; rec
         )
open import Base.Decide
  hiding ( ind
         ; rec
         )

infix 0 if_then_else_

open import Agda.Builtin.Bool
  public
  renaming ( Bool  to 𝟚
           ; false to 0₂
           ; true  to 1₂
           )

ind :
  ∀ {ℓ}
    (P : 𝟚 → Type ℓ)
  → P 0₂
  → P 1₂
  → Π 𝟚 P
ind P f t 0₂ = f
ind P f t 1₂ = t

rec : ∀ {ℓ} {P : Type ℓ} → P → P → 𝟚 → P
rec = ind _

if_then_else_ : ∀ {ℓ} {A : Type ℓ} → 𝟚 → A → A → A
if b then t else f = rec f t b

instance
  DecEq:𝟚 : ∀ {x y : 𝟚} → Decide (x ≡ y)
  DecEq:𝟚 {0₂} {0₂} = yes refl
  DecEq:𝟚 {0₂} {1₂} = no (λ ())
  DecEq:𝟚 {1₂} {0₂} = no (λ ())
  DecEq:𝟚 {1₂} {1₂} = yes refl

_⊕_ : 𝟚 → 𝟚 → 𝟚
0₂ ⊕ 0₂ = 0₂
0₂ ⊕ 1₂ = 1₂
1₂ ⊕ 0₂ = 1₂
1₂ ⊕ 1₂ = 0₂

abstract

  ⊕-assoc : Associative _⊕_
  ⊕-assoc 0₂ 0₂ 0₂ = refl
  ⊕-assoc 0₂ 0₂ 1₂ = refl
  ⊕-assoc 0₂ 1₂ 0₂ = refl
  ⊕-assoc 0₂ 1₂ 1₂ = refl
  ⊕-assoc 1₂ 0₂ 0₂ = refl
  ⊕-assoc 1₂ 0₂ 1₂ = refl
  ⊕-assoc 1₂ 1₂ 0₂ = refl
  ⊕-assoc 1₂ 1₂ 1₂ = refl

  ⊕-comm : Commutative _⊕_
  ⊕-comm 0₂ 0₂ = refl
  ⊕-comm 0₂ 1₂ = refl
  ⊕-comm 1₂ 0₂ = refl
  ⊕-comm 1₂ 1₂ = refl

  ⊕-0₂-left-id : LeftIdentity _⊕_ 0₂
  ⊕-0₂-left-id 0₂ = refl
  ⊕-0₂-left-id 1₂ = refl

  ⊕-0₂-right-id : RightIdentity _⊕_ 0₂
  ⊕-0₂-right-id 0₂ = refl
  ⊕-0₂-right-id 1₂ = refl

  ⊕-0₂-id-left-inv : LeftInverse _⊕_ 0₂ id
  ⊕-0₂-id-left-inv 0₂ = refl
  ⊕-0₂-id-left-inv 1₂ = refl

  ⊕-0₂-id-right-inv : RightInverse _⊕_ 0₂ id
  ⊕-0₂-id-right-inv 0₂ = refl
  ⊕-0₂-id-right-inv 1₂ = refl
