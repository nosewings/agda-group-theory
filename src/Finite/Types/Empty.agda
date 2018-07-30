module Finite.Types.Empty where

open import Base.Sigma
open import Base.Empty

open import Finite.UVec

𝟘-UVec : UVec 𝟘 0
𝟘-UVec = []

𝟘-UVec-Enumeration : Enumeration 𝟘-UVec
𝟘-UVec-Enumeration = λ()

𝟘-Size : Size 𝟘 0
𝟘-Size = 𝟘-UVec , 𝟘-UVec-Enumeration

𝟘-Finite : Finite 𝟘
𝟘-Finite = _ , 𝟘-Size
