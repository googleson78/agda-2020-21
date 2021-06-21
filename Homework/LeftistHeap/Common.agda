module Homework.LeftistHeap.Common where

open import Lib.Nat
open import Lib.One
open import Lib.Zero
open import Lib.Sum
open import Lib.Eq

Leq : Nat -> Nat -> Set
Leq zero m = One
Leq (suc n) zero = Zero
Leq (suc n) (suc m) = Leq n m

decLeq : (n m : Nat) -> Leq n m + Leq m n
decLeq zero m = inl <>
decLeq (suc n) zero = inr <>
decLeq (suc n) (suc m) = decLeq n m

<=-Leq : {n m : Nat} -> n <= m -> Leq n m
<=-Leq ozero = <>
<=-Leq (osuc p) = <=-Leq p

Leq-refl : (n : Nat) -> Leq n n
Leq-refl n = <=-Leq (<=-refl n)

Leq-trans : (n m k : Nat) -> Leq n m -> Leq m k -> Leq n k
Leq-trans zero m k p q = <>
Leq-trans (suc n) (suc m) (suc k) p q = Leq-trans n m k p q

Priority : Set
Priority = Nat

Rank : Set
Rank = Nat

data Maybe (A : Set) : Set where
  no : Maybe A
  yes : A -> Maybe A

min : Nat -> Nat -> Nat
min = {!!}

min-Leq-left : (n m : Nat) -> Leq (min n m) n
min-Leq-left = {!!}

min-right-zero : (m : Nat) -> min m zero == zero
min-right-zero = {!!}

min-symm : (n m : Nat) -> min n m == min m n
min-symm = {!!}

min-Leq-right : (n m : Nat) -> Leq (min n m) m
min-Leq-right = {!!}
