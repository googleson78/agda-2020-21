module Lib.Vec where

open import Lib.Nat

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _,-_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

infixr 11 _,-_


_+V_ : {A : Set} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n +N m)
[] +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)

infixr 12 _+V_


vHead : {A : Set} {n : Nat} -> Vec A (suc n) -> A
vHead (x ,- _) = x
