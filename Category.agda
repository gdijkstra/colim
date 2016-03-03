{-# OPTIONS --without-K #-}

module Category where

open import lib.Basics

record Cat {l : ULevel} : Type (lsucc (lsucc l)) where
  field
    obj : Type (lsucc l)
    hom : obj → obj → Type l
    comp : {X Y Z : obj} → hom Y Z → hom X Y → hom X Z
    assoc : {X Y Z W : obj} (h : hom Z W) (g : hom Y Z) (f : hom X Y)
          → comp (comp h g) f == comp h (comp g f)

TypeCat : Cat
TypeCat = record
  { obj  = Type0  
  ; hom  = (λ A B → A → B)
  ; comp = (λ g f x → g (f x))
  ; assoc = (λ h g f → idp)
  }

/_/ : Cat → Type1
/ 𝓒 / = Cat.obj 𝓒

_[_,_] : (𝓒 : Cat) → Cat.obj 𝓒 → Cat.obj 𝓒 → Type0
𝓒 [ A , B ] = Cat.hom 𝓒 A B

record Func (𝓒 𝓓 : Cat) : Type1 where
  field
    obj : / 𝓒 / → / 𝓓 /
    hom : {A B : / 𝓒 /} → 𝓒 [ A , B ] → 𝓓 [ obj A , obj B ]
    hom-∘ : {A B C : / 𝓒 /} (g : 𝓒 [ B , C ]) (f : 𝓒 [ A , B ]) → hom (Cat.comp 𝓒 g f) == Cat.comp 𝓓 (hom g) (hom f)

_⋆_ : {𝓒 𝓓 : Cat} (F : Func 𝓒 𝓓) → / 𝓒 / → / 𝓓 /
F ⋆ X = Func.obj F X

_⋆⋆_ : {𝓒 𝓓 : Cat} (F : Func 𝓒 𝓓) {A B : / 𝓒 /} → 𝓒 [ A , B ] → 𝓓 [ F ⋆ A , F ⋆ B ]
F ⋆⋆ f = Func.hom F f

_⇒_ : Cat → Cat → Type1
𝓒 ⇒ 𝓓 = Func 𝓒 𝓓
