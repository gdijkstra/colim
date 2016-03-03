{-# OPTIONS --without-K #-}

open import Category

module Alg (𝓒 : Cat) (F : 𝓒 ⇒ 𝓒) where

open import UIP
open import lib.Basics

infixr 80 _∘-𝓒_
_∘-𝓒_ = Cat.comp 𝓒

record Alg : Type1 where
  constructor alg
  field
    X : / 𝓒 /
    θ : 𝓒 [ F ⋆ X , X ]
    
record AlgHom (𝓧 𝓨 : Alg) : Type0 where
  constructor alghom

  open Alg 𝓧
  open Alg 𝓨 renaming (X to Y ; θ to ρ)

  field
    f : 𝓒 [ X , Y ]
    f₀ : f ∘-𝓒 θ == ρ ∘-𝓒 (F ⋆⋆ f)

_▸_ :
  {X Y Z : / 𝓒 /}
  (g : 𝓒 [ Y , Z ])
  {f f' : 𝓒 [ X , Y ]}
  (p : f == f')
  → g ∘-𝓒 f == g ∘-𝓒 f'
g ▸ p = ap (λ h → g ∘-𝓒 h) p  

_◂_ :
  {X Y Z : / 𝓒 /}
  {g g' : 𝓒 [ Y , Z ]}
  (p : g == g')
  (f : 𝓒 [ X , Y ])
  → g ∘-𝓒 f == g' ∘-𝓒 f
p ◂ f = ap (λ h → h ∘-𝓒 f) p  

module _ {𝓧 𝓨 : Alg} where
  open Alg 𝓧
  open Alg 𝓨 renaming (X to Y ; θ to ρ)

  alg-hom-eq :
    (f g : 𝓒 [ X , Y ])
    (f₀ : f ∘-𝓒 θ == ρ ∘-𝓒 (F ⋆⋆ f))
    (g₀ : g ∘-𝓒 θ == ρ ∘-𝓒 (F ⋆⋆ g))
    → (f == g)
    → alghom f f₀ == alghom g g₀
  alg-hom-eq f .f f₀ g₀ idp = ap (alghom f) (uip f₀ g₀)

module _ {𝓧 𝓨 𝓩 : Alg} where
  open Alg 𝓧
  open Alg 𝓨 renaming (X to Y ; θ to ρ)
  open Alg 𝓩 renaming (X to Z ; θ to ζ)

  _∘-Alg_ : AlgHom 𝓨 𝓩 → AlgHom 𝓧 𝓨 → AlgHom 𝓧 𝓩
  (alghom g g₀) ∘-Alg (alghom f f₀) =
    alghom (g ∘-𝓒 f)
           ((g ∘-𝓒 f) ∘-𝓒 θ
            =⟨ Cat.assoc 𝓒 g f θ ⟩
           g ∘-𝓒 (f ∘-𝓒 θ)
            =⟨ g ▸ f₀ ⟩
           g ∘-𝓒 (ρ ∘-𝓒 (F ⋆⋆ f))
            =⟨ ! (Cat.assoc 𝓒 g ρ (F ⋆⋆ f)) ⟩
           (g ∘-𝓒 ρ) ∘-𝓒 (F ⋆⋆ f)
            =⟨ g₀ ◂ (F ⋆⋆ f) ⟩
           (ζ ∘-𝓒 (F ⋆⋆ g)) ∘-𝓒 (F ⋆⋆ f)
            =⟨ Cat.assoc 𝓒 ζ (F ⋆⋆ g) (F ⋆⋆ f) ⟩
           ζ ∘-𝓒 ((F ⋆⋆ g) ∘-𝓒 (F ⋆⋆ f))
            =⟨ ζ ▸ ! (Func.hom-∘ F g f) ⟩
           ζ ∘-𝓒 (F ⋆⋆ g ∘-𝓒 f) ∎)

  infixr 80 _∘-Alg_

AlgCat : Cat
AlgCat = record
  { obj = Alg
  ; hom = AlgHom
  ; comp = _∘-Alg_
  ; assoc = λ h g f → alg-hom-eq _ _ _ _ (Cat.assoc 𝓒 _ _ _)
  }
