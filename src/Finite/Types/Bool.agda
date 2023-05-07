module Finite.Types.Bool where

open import Base.Sigma
open import Base.Equality
open import Base.Bool
  as 𝟚

open import Finite.UList

𝟚-UList : UList 𝟚
𝟚-UList = 0₂ ∷ (1₂ ∷ [] and []) and ((λ()) ∷ [])

instance

  𝟚-UVec-Enumeration : Enumeration 𝟚-UList
  𝟚-UVec-Enumeration = intro (𝟚.ind _ (here refl) (there (here refl)))

  𝟚-Finite : Finite 𝟚
  𝟚-Finite = intro 𝟚-UList
