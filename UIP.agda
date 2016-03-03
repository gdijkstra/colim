-- We want to make explicit where we use UIP, so we will still tag
-- other files as "without K" and import this module where needed.

module UIP where

open import lib.Basics

uip : {A : Type0} {x y : A} (p q : x == y) → p == q
uip idp idp = idp
