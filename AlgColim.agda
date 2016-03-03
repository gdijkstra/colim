{-# OPTIONS --without-K #-}

open import Category

module AlgColim (𝓒 : Cat) (F : 𝓒 ⇒ 𝓒) where

open Cat
open import UIP
open import lib.Basics
open import lib.types.Nat
open import Colim
open import Alg

module _
  (𝓒-colims : has-seq-colims 𝓒)
  (F-preserves-colims : preserves-seq-colims 𝓒 F)
  (C : Cochain (AlgCat 𝓒 F)) where

  open Cochain (AlgCat 𝓒 F) C renaming (X to 𝓧 ; x to 𝔁)

  X : ℕ → / 𝓒 /
  X n = Alg.X (𝓧 n)

  θ : (n : ℕ) → 𝓒 [ F ⋆ (X n) , X n ]
  θ n = Alg.θ (𝓧 n)
  
  f : (n : ℕ) → 𝓒 [ X n , X (S n) ]
  f n = AlgHom.f (𝔁 n)

  f₀ : (n : ℕ) → comp 𝓒 (f n) (θ n) == comp 𝓒 (θ (S n)) (F ⋆⋆ f n)
  f₀ n = AlgHom.f₀ (𝔁 n)

  D : Cochain 𝓒
  D = cochain X f

  colim-in-𝓒 : Colim 𝓒 D
  colim-in-𝓒 = 𝓒-colims D

  -- TODO: the rest

