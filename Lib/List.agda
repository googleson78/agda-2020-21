module Lib.List where

open import Lib.Eq
open import Lib.Nat
open import Lib.One
open import Lib.Sigma

data List (a : Set) : Set where
  [] : List a
  _,-_ : a -> List a -> List a

infixr 11 _,-_

-- concatenate two lists
_+L_ : {A : Set} -> List A -> List A -> List A
[] +L ys = ys
(x ,- xs) +L ys = x ,- (xs +L ys)

infixr 12 _+L_

+L-assoc : {A : Set} (xs ys zs : List A) -> (xs +L ys) +L zs == xs +L (ys +L zs)
+L-assoc [] ys zs = refl
+L-assoc (x ,- xs) ys zs = ap (x ,-_) (+L-assoc xs ys zs)

+L-right-id : {A : Set} (xs : List A) -> xs +L [] == xs
+L-right-id [] = refl
+L-right-id (x ,- xs) = ap (x ,-_) (+L-right-id xs)

length : {A : Set} -> List A -> Nat
length [] = zero
length (_ ,- xs) = suc (length xs)

All : {X : Set} (P : X -> Set) -> List X -> Set
All _ [] = One
All P (x ,- xs) = P x * All P xs
