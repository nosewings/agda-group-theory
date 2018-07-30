module Base.List.One where

open import Base.Type
open import Base.Type.Negation
  as ¬
open import Base.Pi
open import Base.Sigma
open import Base.Product
open import Base.Equality
open import Base.List.Core
  as List
import Base.List.All
  as ListAll
import Base.List.Any
  as ListAny

open import Base.List.Core
  public
  using ( One
        ; here
        ; nothere
        )

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {P : A → Type ℓ₂} where

  to-Any : {xs : List A} → One P xs → Any P xs
  to-Any (here    Px _    ) = here Px
  to-Any (nothere _  ∃!xsP) = there (to-Any ∃!xsP)

  modify : (∀ x → P x → A) → {xs : List A} → One P xs → List A
  modify f = ListAny.modify f ∘ to-Any

  extract : {xs : List A} → One P xs → Σ[ x ] (x ∈! xs × P x)
  extract (here    Px   ∀xs¬P) = _ , here refl (ListAll.map (λ{ x ¬Px refl → Px ⊥ ¬Px }) ∀xs¬P) , Px
  extract (nothere ¬Py  ∃!xsP) = let (x , x∈xs , Px) = extract ∃!xsP
                                 in x , nothere (¬.contramap (λ{ refl → Px }) ¬Py) x∈xs , Px

  remove : {xs : List A} → One P xs → List A × Σ[ x ] P x
  remove = ListAny.remove ∘ to-Any

  remove-All¬ : {xs : List A} (∃!xsP : One P xs) → All (¬_ ∘ P) (proj₁ (remove ∃!xsP))
  remove-All¬ (here    _   ∀xs¬P) = ∀xs¬P
  remove-All¬ (nothere ¬Px ∃!xsP) = ¬Px ∷ remove-All¬ ∃!xsP

map-over :
  ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
    {A : Type ℓ₁} {B : Type ℓ₂} {P : A → Type ℓ₃} {Q : B → Type ℓ₄}
    {f : A → B}
  → (∀ x → P x     → Q (f x))
  → (∀ x → Q (f x) → P x    )
  → {xs : List A}
  → One P xs → One Q (List.map f xs)
map-over P⇒Qf Qf⇒P (here    Px  ∀xs¬P) = here    (P⇒Qf   _ Px )             (ListAll.map-over (¬.contramap ∘ Qf⇒P) ∀xs¬P)
map-over P⇒Qf Qf⇒P (nothere ¬Px ∃!xsP) = nothere (¬.contramap (Qf⇒P _) ¬Px) (map-over P⇒Qf Qf⇒P ∃!xsP)
