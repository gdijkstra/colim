{-# OPTIONS --without-K #-}

open import Category

module Colim (𝓒 : Cat) where

open import lib.Basics
open import lib.types.Nat

record Cochain : Type1 where
  field
    X : ℕ → / 𝓒 /
    x : (n : ℕ) → 𝓒 [ X n , X (S n) ]

infixr 80 _∘-𝓒_
_∘-𝓒_ = Cat.comp 𝓒

module _ (C : Cochain) where
  open Cochain C
  
  record CoconeObj : Type1 where
    field
      A : / 𝓒 /
      i : (n : ℕ) → 𝓒 [ X n , A ]
      g : (n : ℕ) → (i (S n)) ∘-𝓒 (x n) == i n
  
  record CoconeHom (𝓐 𝓑 : CoconeObj) : Type1 where
    open CoconeObj 𝓐
    open CoconeObj 𝓑 renaming (A to B ; i to j ; g to h)
  
    field
      f : 𝓒 [ A , B ]
      f₀ : (n : ℕ) → f ∘-𝓒 i n == j n
      --f₁ : (n : ℕ) → {!!}

  is-seq-colim : CoconeObj → Type1
  is-seq-colim 𝓐 = (𝓑 : CoconeObj) → is-contr (CoconeHom 𝓐 𝓑)

