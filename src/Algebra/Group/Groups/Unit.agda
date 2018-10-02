module Algebra.Group.Groups.Unit where

open import Base.Type
open import Base.Pi
open import Base.Equality
open import Base.Unit
open import Algebra.Group

instance
  Group:𝟙 : Group 𝟙
  Group:𝟙 = record
    { _·_       = const (const _)
    ; ε         = _
    ; _⁻¹       = const _
    ; assoc     = const (const (const refl))
    ; left-id   = const refl
    ; right-id  = const refl
    ; left-inv  = const refl
    ; right-inv = const refl
    }
