module Lib.Zero where

data Zero : Set where

zero-elim : {A : Set} -> Zero -> A
zero-elim ()
