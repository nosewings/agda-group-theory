module Base.Type.Equivalence where

open import Base.Type
open import Base.Type.LogicalEquivalence
open import Base.Pi
  as Π
open import Base.Sigma
open import Base.Relation
  as Relation
open import Base.Equality

open import Base.Type.Equivalence.Core
  public

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} where

  from-inj-and-surj : {f : A → B} → Injective f → SplitSurjective f → A ≅ B
  from-inj-and-surj {f} inj surj = _≅_.intro (_↔_.intro f g) (_⇄_.intro η ε) where

    g : B → A
    g = proj₁ Π.∘ surj

    abstract

      ε : f Π.∘ g ≐ Π.id
      ε = proj₂ Π.∘ surj

      η : Π.id ≐ g Π.∘ f
      η = Relation.sym Π.∘ inj Π.∘ ε Π.∘ f

module _ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (A≅B : A ≅ B) where

  open _≅_ A≅B
    renaming ( to   to f
             ; from to g
             )
  open _⇄_ to⇄from
    renaming ( unit   to η
             ; counit to ε
             )

  open ≡Reasoning

  abstract

    to-inj : Injective f
    to-inj {x} {y} f[x]≡f[y] =
        x       ≡⟨ η x ⟩
        g (f x) ≡⟨ cong g f[x]≡f[y] ⟩
        g (f y) ≡⟨ η y ⟩⁻¹
        y       ∎

    from-inj : Injective g
    from-inj {x} {y} g[x]≡g[y] =
        x       ≡⟨ ε x ⟩⁻¹
        f (g x) ≡⟨ cong f g[x]≡g[y] ⟩
        f (g y) ≡⟨ ε y ⟩
        y       ∎

  to-surj : SplitSurjective f
  to-surj y = g y , ε y

  from-surj : SplitSurjective g
  from-surj x = f x , Relation.sym η x
