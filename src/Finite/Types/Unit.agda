module Finite.Types.Unit where

open import Base.Sigma
open import Base.Equality
open import Base.Unit

open import Finite.UVec

𝟙-UVec : UVec 𝟙 1
𝟙-UVec = _ ∷ [] and []

𝟙-UVec-Enumeration : Enumeration 𝟙-UVec
𝟙-UVec-Enumeration = λ _ → here refl

𝟙-Size : Size 𝟙 1
𝟙-Size = 𝟙-UVec , 𝟙-UVec-Enumeration

𝟙-Finite : Finite 𝟙
𝟙-Finite = _ , 𝟙-Size
