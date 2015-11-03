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
open import lib.Equivalences

-- We want to take the colimit of the sequence:
--
--   ⊥ → F ⊥ → F² ⊥ → F³ ⊥ → ...

module _ (F : Container) where
  open Container F renaming (S to S' ; P to P')

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

  -- Shift the chain by one, which is the same as shifting by applying
  -- F.
  D' : ℕ → Type0
  D' = D ∘ S

  d' : (n : ℕ) → D' n → D' (S n)
  d' n x = d (S n) x

  μF' : Type0
  μF' = ℕColim d'

  i' : (n : ℕ) → D' n → μF'
  i' = ncin {D = D'} {d = d'}

  g' : (n : ℕ) (x : D' n) → i' n x == i' (S n) (d' n x)
  g' = ncglue {D = D'} {d = d'}

  -- μF and μF' are equivalent
  module μF≃μF' where
    open ℕColimRec d renaming (f to rec)
    open ℕColimRec d' renaming (f to rec')

    to : μF → μF'
    to = rec (λ n x → i' n (d n x)) (λ n x → g' n (d n x))

    from : μF' → μF
    from = rec' (λ n x → i (S n) x) (λ n x → g (S n) x)

      -- to (from (i' n x))
      --  =⟨ idp ⟩ -- β for rec'
      -- to (i (S n) x)
      --  =⟨ idp ⟩ -- β for rec
      -- i' (S n) (d (S n) x)
      --  =⟨ ! (g' n x) ⟩
      -- i' n x 
    to-from : (x : μF') → x == to (from x)
    to-from = ℕColim-elim d' g' (λ n x → {!!}) -- use transport of λ x . f x == g x rules

    from-to : (x : μF) → x == from (to x)
    from-to = ℕColim-elim d g (λ n x → {!!}) -- same

    μF≃μF' : μF ≃ μF'
    μF≃μF' = equiv to from (! ∘ to-from) (! ∘ from-to)

  -- μF' and F μF are equivalent

  module μF'≃FμF where
    open ℕColimRec d' renaming (f to rec')

    to : μF' → ⟦ F ⟧₀ μF
    to = rec' (λ n x → ⟦ F ⟧₁ (i n) x) (λ n x → {!!}) -- should be ap something g

    from : ⟦ F ⟧₀ μF → μF'
    from = {!!}

    
