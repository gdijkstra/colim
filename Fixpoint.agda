{-# OPTIONS --without-K #-}

-- Constructing fixpoints of an endofunctor as a homotopy colimit.

module Fixpoint where

open import lib.Base hiding (S)

record Container : Type1 where
  constructor mk-cont
  field
    S : Type0
    P : S → Type0

⟦_⟧₀ : Container → Type0 → Type0
⟦ mk-cont S P ⟧₀ X = Σ S (λ s → P s → X)

⟦_⟧₁ : (F : Container) {X Y : Type0}
     → (X → Y) → ⟦ F ⟧₀ X → ⟦ F ⟧₀ Y
⟦ mk-cont S P ⟧₁ f (s , t) = (s , f ∘ t)

open import lib.types.NatColim
open import lib.types.Nat
open import lib.types.Empty
open import lib.Funext using (λ=)
open import lib.PathGroupoid

-- We want to take the colimit of the sequence:
--
--   ⊥ → F ⊥ → F² ⊥ → F³ ⊥ → ...

module _ (F : Container) where
  D : ℕ → Type0
  D O     = ⊥
  D (S n) = ⟦ F ⟧₀ (D n)

  d : (n : ℕ) → D n → D (S n)
  d O ()
  d (S n) = ⟦ F ⟧₁ (d n)

  μF : Type0
  μF = ℕColim d

  i : (n : ℕ) → D n → μF
  i = ncin {D = D} {d = d}

  g : (n : ℕ) (x : D n) → i n x == i (S n) (d n x)
  g = ncglue {D = D} {d = d}

  g-ext : (n : ℕ) → i n == i (S n) ∘ d n
  g-ext n = λ= (g n)

  open ℕColimRec d renaming (f to rec)

  c : (n : ℕ) → D n → ⟦ F ⟧₀ μF
  c O ()
  c (S n) = ⟦ F ⟧₁ (i n)

  p : (n : ℕ) (x : D n) → c n x == c (S n) (d n x)
  p O ()
  p (S n) x =
    ⟦ F ⟧₁ (i n) x
     =⟨ ap (λ h → ⟦ F ⟧₁ h x) (g-ext n) ⟩
    ⟦ F ⟧₁ (i (S n) ∘ d n) x
     =⟨ idp ⟩ -- Functor laws hold strictly for containers
    ⟦ F ⟧₁ (i (S n)) (⟦ F ⟧₁ (d n) x) ∎

  out : μF → ⟦ F ⟧₀ μF
  out = rec c p

  -- Note that F preserves this colimit:
  i' : (n : ℕ) → D n → ⟦ F ⟧₀ μF
  i' n = out ∘ i n

  g' : (n : ℕ) (x : D n) → i' n x == i' (S n) (d n x)
  g' n = ap out ∘ g n

  g'-ext : (n : ℕ) → i' n == i' (S n) ∘ d n
  g'-ext n = λ= (g' n)

  FμF-rec :
    {A : Type0}
    (i* : (n : ℕ) → D n → A)
    (g* : (n : ℕ) (x : D n) → i* n x == i* (S n) (d n x))
    → ⟦ F ⟧₀ μF → A
  FμF-rec i* g* (s , t) = {!!}

  -- The above function should be unique however to be fully precise.

  inn : ⟦ F ⟧₀ μF → μF
  inn = FμF-rec i g

  open import lib.Univalence
  open import lib.Equivalences

  μF=FμF : μF == ⟦ F ⟧₀ μF
  μF=FμF = ua (equiv out inn {!!} {!!})
