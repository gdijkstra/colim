{-# OPTIONS --without-K #-}

open import Category

module Alg (𝓒 : Cat) (F : 𝓒 ⇒ 𝓒) where

open import lib.Basics

infixr 80 _∘-𝓒_
_∘-𝓒_ = Cat.comp 𝓒

record Alg : Type1 where
  constructor alg
  field
    X : / 𝓒 /
    θ : 𝓒 [ F ⋆ X , X ]
    
record AlgHom (𝓧 𝓨 : Alg) : Type1 where
  constructor alghom

  open Alg 𝓧
  open Alg 𝓨 renaming (X to Y ; θ to ρ)

  field
    f : 𝓒 [ X , Y ]
    f₀ : f ∘-𝓒 θ == ρ ∘-𝓒 (F ⋆⋆ f)

-- need assoc for this
-- infixr 80 _∘-Alg_
-- _∘-Alg_ : {𝓧 𝓨 𝓩 : Alg} → AlgHom 𝓨 𝓩 → AlgHom 𝓧 𝓨 → AlgHom 𝓧 𝓩
-- (alghom g g₀) ∘-Alg (alghom f f₀) = alghom (g ∘-𝓒 f) {!!}
