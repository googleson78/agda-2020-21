module Lib.Nat where

open import Lib.Eq

data Nat : Set where
  zero : Nat -- zero
  suc : Nat -> Nat -- 1+

-- allows us to write literals
-- also means that Nat will compile to Integer in hs
{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

infixr 15 _+N_

+N-right-zero : (n : Nat) -> n +N 0 == n
+N-right-zero zero = refl zero
+N-right-zero (suc n') = ap suc (+N-right-zero n')

+N-assoc : (n m k : Nat) -> (n +N m) +N k == n +N (m +N k)
+N-assoc zero m k = refl (m +N k)
+N-assoc (suc n) m k rewrite +N-assoc n m k = refl _

data _<=_ : Nat -> Nat -> Set where
  ozero : {n : Nat} -> 0 <= n
  osuc : {n m : Nat} -> n <= m -> suc n <= suc m

infix 9 _<=_

<=-trans : {n m k : Nat} -> n <= m -> m <= k -> n <= k
<=-trans ozero q = ozero
<=-trans (osuc p) (osuc q) = osuc (<=-trans p q)

+N-right-suc : (n m : Nat) -> n +N suc m == suc (n +N m)
+N-right-suc zero m = refl (suc m)
+N-right-suc (suc n) m = ap suc (+N-right-suc n m)

+N-commut : (n m : Nat) -> n +N m == m +N n
+N-commut zero m = ==-symm (+N-right-zero m)
+N-commut (suc n) m rewrite (+N-commut n m) = ==-symm (+N-right-suc m n)
