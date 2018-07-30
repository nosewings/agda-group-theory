module Finite.Types.Bool where

open import Base.Sigma
open import Base.Equality
open import Base.Bool
  as 𝟚

open import Finite.UVec

𝟚-UVec : UVec 𝟚 2
𝟚-UVec = 0₂ ∷ (1₂ ∷ [] and []) and ((λ()) ∷ [])

𝟚-UVec-Enumeration : Enumeration 𝟚-UVec
𝟚-UVec-Enumeration = 𝟚.ind (_∈ 𝟚-UVec) (here refl) (there (here refl))

𝟚-Size : Size 𝟚 2
𝟚-Size = 𝟚-UVec , 𝟚-UVec-Enumeration

𝟚-Finite : Finite 𝟚
𝟚-Finite = _ , 𝟚-Size
