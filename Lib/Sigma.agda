module Lib.Sigma where

record _*_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _*_ public
