module Lib.Sigma where

record _><_ (A : Set) (P : A -> Set) : Set where
  constructor _,_
  field
    fst : A
    snd : P fst

infixr 8 _><_
infixr 8 _,_

open _><_ public

_*_ : Set -> Set -> Set
A * B = A >< \ _ -> B

infixr 9 _*_
