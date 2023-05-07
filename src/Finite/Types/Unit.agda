module Finite.Types.Unit where

open import Base.Pi
open import Base.Sigma
open import Base.Equality
open import Base.Unit

open import Finite.UList

𝟙-UList : UList 𝟙
𝟙-UList = _ ∷ [] and []

instance

  𝟙-UVec-Enumeration : Enumeration 𝟙-UList
  𝟙-UVec-Enumeration = intro (const (here refl))

  𝟙-Finite : Finite 𝟙
  𝟙-Finite = intro 𝟙-UList
