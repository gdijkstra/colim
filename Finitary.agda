{-# OPTIONS --without-K #-}

-- Finitary containers
module Finitary where

open import lib.Base
open import lib.types.Nat
open import Fin

record FinCont : Type1 where
  constructor mk-fin-cont
  field
    Sh : Type0
    Pos : Sh → ℕ

⟦_⟧₀ : FinCont → Type0 → Type0
⟦ mk-fin-cont A B ⟧₀ X = Σ A (λ s → Fin (B s) → X)

⟦_⟧₁ : (F : FinCont) {X Y : Type0}
     → (X → Y) → ⟦ F ⟧₀ X → ⟦ F ⟧₀ Y
⟦ mk-fin-cont A B ⟧₁ f (s , t) = (s , f ∘ t)

_∘-FinCont_ : FinCont → FinCont → FinCont
mk-fin-cont C D ∘-FinCont mk-fin-cont A B =
  mk-fin-cont (Σ C (λ c → Fin (D c) → A))
              (λ { (c , f) → sum (D c) (B ∘ f) })

module ∘-Correct (F G : FinCont) (X : Type0) where
  open FinCont F renaming (Sh to A ; Pos to B)
  open FinCont G renaming (Sh to C ; Pos to D)

  to : ⟦ F ⟧₀ (⟦ G ⟧₀ X) -> ⟦ F ∘-FinCont G ⟧₀ X
  to (a , b) = (a , fst ∘ b) , (λ x → (uncurry (snd ∘ b)) (fsigmacase (B a) (D ∘ fst ∘ b) x))

  from : ⟦ F ∘-FinCont G ⟧₀ X → ⟦ F ⟧₀ (⟦ G ⟧₀ X)
  from ((a , c) , t) = a , (λ x → (c x) , (t ∘ fdpair (B a) (D ∘ c) x))

  open import lib.Funext using (λ=)

  -- Doing this directly is messy because of the with-patterns.
  from-to : (x : ⟦ F ⟧₀ (⟦ G ⟧₀ X)) → from (to x) == x
  from-to (a , b) = ap (λ x → a , x) (λ= (λ x → pair= idp (λ= (λ x' → {!!}))))

  to-from : (x : ⟦ F ∘-FinCont G ⟧₀ X) → to (from x) == x
  to-from ((a , c) , t) = ap (λ x → (a , c) , x) (λ= (λ x → {!!}))



