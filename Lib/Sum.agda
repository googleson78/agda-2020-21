module Lib.Sum where

open import Lib.Zero

data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

infixr 8 _+_

data Dec (A : Set) : Set where
  no : (A -> Zero) -> Dec A
  yes : A -> Dec A
