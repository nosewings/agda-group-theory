module Algebra.Group.Groups.Bool where

open import Base.Type
open import Base.Pi
open import Base.Equality
open import Base.Bool
open import Algebra.Group

instance
  Group:𝟚 : Group 𝟚
  Group:𝟚 = record
    { _·_       = _⊕_
    ; ε         = 0₂
    ; _⁻¹       = id
    ; assoc     = ⊕-assoc
    ; left-id   = ⊕-0₂-left-id
    ; right-id  = ⊕-0₂-right-id
    ; left-inv  = ⊕-0₂-id-left-inv
    ; right-inv = ⊕-0₂-id-right-inv
    }
