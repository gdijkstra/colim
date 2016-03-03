{-# OPTIONS --without-K #-}

open import Category

module Colim (𝓒 : Cat) where

open import lib.Basics
open import lib.types.Nat
open import UIP

record Cochain : Type1 where
  constructor cochain

  field
    X : ℕ → / 𝓒 /
    x : (n : ℕ) → 𝓒 [ X n , X (S n) ]

infixr 80 _∘-𝓒_
_∘-𝓒_ = Cat.comp 𝓒

module _ (C : Cochain) where
  open Cochain C
  
  record CoconeObj : Type1 where
    constructor cocone

    field
      A : / 𝓒 /
      i : (n : ℕ) → 𝓒 [ X n , A ]
      g : (n : ℕ) → (i (S n)) ∘-𝓒 (x n) == i n
  
  record CoconeHom (𝓐 𝓑 : CoconeObj) : Type0 where
    open CoconeObj 𝓐
    open CoconeObj 𝓑 renaming (A to B ; i to j ; g to h)
  
    field
      f : 𝓒 [ A , B ]
      f₀ : (n : ℕ) → f ∘-𝓒 i n == j n
      --f₁ : (n : ℕ) → {! path computation rule !}

  is-seq-colim : CoconeObj → Type1
  is-seq-colim 𝓐 = (𝓑 : CoconeObj) → is-contr (CoconeHom 𝓐 𝓑)

  Colim : Type1
  Colim = Σ CoconeObj is-seq-colim

has-seq-colims : Type1
has-seq-colims = (C : Cochain) → Colim C

-- TODO: Have better name for this
apply : (F : 𝓒 ⇒ 𝓒) → Cochain → Cochain
apply F (cochain X x) = cochain (λ n → F ⋆ X n) (λ n → F ⋆⋆ x n)

preserves-seq-colims : (F : 𝓒 ⇒ 𝓒) → Type1
preserves-seq-colims F = (C : Cochain) → Colim C → Colim (apply F C)
