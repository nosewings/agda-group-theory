module Base.Nat where

open import Base.Type
open import Base.Pi
open import Base.Pi.Operation
open import Base.FromNat
open import Base.Relation
  hiding ( refl
         )
open import Base.Equality
open import Base.WellFounded

infix 4 _≤_ _<_ _≤′_ _<′_

open import Base.Nat.Core
  public

fold :
  ∀ {ℓ}
    {A : Type ℓ}
  → (A → A) → A → ℕ → A
fold f e zero     = e
fold f e (succ n) = f (fold f e n)

abstract

  fold-id : ∀ {ℓ} {A : Type ℓ} (e : A) n → fold id e n ≡ e
  fold-id e zero     = refl
  fold-id e (succ n) = fold-id e n

  +-fold : ∀ m n → m + n ≡ fold succ n m
  +-fold zero     n = refl
  +-fold (succ m) n = cong succ (+-fold m n)

  +-assoc : Associative _+_
  +-assoc zero     y z = refl
  +-assoc (succ x) y z = cong succ (+-assoc x y z)

  +-comm : Commutative _+_
  +-comm zero     zero     = refl
  +-comm zero     (succ y) = cong succ (+-comm zero y)
  +-comm (succ x) zero     = cong succ (+-comm x zero)
  +-comm (succ x) (succ y) =
      succ x + succ y     ≡⟨⟩
      succ (x + succ y)   ≡⟨ +-comm x (succ y) |in-context succ ⟩
      succ (succ y + x)   ≡⟨⟩
      succ (succ (y + x)) ≡⟨ +-comm y x |in-context (succ ∘ succ) ⟩
      succ (succ (x + y)) ≡⟨⟩
      succ (succ x + y)   ≡⟨ +-comm (succ x) y |in-context succ ⟩
      succ (y + succ x)   ≡⟨⟩
      succ y + succ x     ∎
    where open ≡Reasoning

  *-fold : ∀ m n → m * n ≡ fold (n +_) zero m
  *-fold zero     n = refl
  *-fold (succ m) n = cong (n +_) (*-fold m n)

data _≤_ : Relation 0 ℕ where
  zero : ∀ {n} → zero ≤ n
  succ : ∀ {m n} → m ≤ n → succ m ≤ succ n

≤succ : ∀ {m n} → m ≤ n → m ≤ succ n
≤succ zero       = zero
≤succ (succ m≤n) = succ (≤succ m≤n)

_≥_ : Relation 0 ℕ
m ≥ n = n ≤ m

_<_ : Relation 0 ℕ
m < n = succ m ≤ n

data _≤′_ (m : ℕ) : ℕ → Type 0 where
  refl : m ≤′ m
  succ : ∀ {n} → m ≤′ n → m ≤′ succ n

_<′_ : Relation 0 ℕ
m <′ n = succ m ≤′ n

<′-wf : WellFounded _<′_
<′-wf = acc ∘ aux where
  aux : ∀ n x → x <′ n → Acc _<′_ x
  aux (succ x) x refl        = <′-wf x
  aux (succ n) x (succ x<′n) = aux n x x<′n

zero≤′ : ∀ n → zero ≤′ n
zero≤′ zero     = refl
zero≤′ (succ n) = succ (zero≤′ n)

succ≤′succ : ∀ {m n} → m ≤′ n → succ m ≤′ succ n
succ≤′succ refl       = refl
succ≤′succ (succ m≤′n) = succ (succ≤′succ m≤′n)
