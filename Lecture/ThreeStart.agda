{-# OPTIONS --no-unicode #-}

module Lecture.ThreeStart where

open import Lib.Nat
open import Lib.Eq
open import Lib.List
open import Lib.One
open import Lib.Zero
open import Lib.Two
open import Lib.Sum

-- !show rewrite

{-
+N-right-zero' : (n : Nat) -> n +N 0 == n
+N-right-zero' = {!!}

-- !show with
-- !don't forget to say what the three dots mean!!
-- !demonstrate that when we match, goal changes
-- !show lambda
-- !?show where
-- !?show "generate helper"
-- dec== : (n m : Nat) -> Bool

Even : Nat -> Set
Even zero = One
Even (suc zero) = Zero -- 1
Even (suc (suc n)) = Even n -- 2 + n

-- !explain how this is an "exists"
-- !examples!
-- !do these on another "live solving session" instead:
-- show how this generalises _+_ ?
-- and how (a : A) -> P a generalises _*_ ?
record _><_ ?? : Set where

open _><_ public

infixr 8 _><_

_*_ : Set -> Set -> Set
A * B = ?
infixr 9 _*_

difference<= : (m n : Nat) -> n <= m -> Nat >< \d -> m == n +N d
difference<= = ?

data Vec (A : Set) : Nat -> Set where

vHead : {A : Set} {n : Nat} -> ?
vHead = ?

vTail : {A : Set} {n : Nat} -> ?
vTail = ?

-- !?show parallel with +L - agda can now write it itself
_+V_ : ?
_+V_ = ?

infixr 12 _+V_

listToVec : {A : Set} -> List A -> Nat >< Vec A
listToVec = ?

_=[]_ : {A : Set} {y : A} -> (x : A) -> x == y -> x == y
x =[] (refl _) = refl _

infixr 1 _=[]_

_=[_>=_ : {A : Set} {y z : A} -> (x : A) -> x == y -> y == z -> x == z
x =[ refl _ >= (refl _) = refl _

infixr 1 _=[_>=_

_=<_]=_ : {A : Set} {y z : A} -> (x : A) -> y == z -> x == y -> x == z
x =< refl _ ]= (refl _) = refl _

infixr 1 _=<_]=_

_QED : {A : Set} -> (x : A) -> x == x
x QED = refl x

infix 3 _QED

-- ! show =[] for zero case?
-- ! show eq reasoning with commut
-- ! maybe write out eq reasoning?

+N-commut' : (n m : Nat) -> n +N m == m +N n
+N-commut' = {!!}

-}

{-

<=-refl : (n : Nat) -> n <= n
<=-refl = ?

<=-antisym : {n m : Nat} -> n <= m -> m <= n -> n == m
<=-antisym = {!!}

<=-mono-left-+ : {n m : Nat} (k : Nat) -> n <= m -> k +N n <= k +N m
<=-mono-left-+ = {!!}

-- you might need a lemma here
<=-mono-right-+ : {n m : Nat} (k : Nat) -> n <= m -> n +N k <= m +N k
<=-mono-right-+ = {!!}

-- multiplication using repeated addition
_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N n *N m
infixr 40 _*N_

-- EXERCISE: multiplication right identity
*N-right-id : (n : Nat) -> n *N 1 == n
*N-right-id = {!!}

-- multiplication distributes over addition
*N-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
*N-distrib-+N = {!!}

-- use *N-distrib-+N
*N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
*N-assoc = {!!}

-- figure out what lemmas you need
*N-commut : (n m : Nat) -> n *N m == m *N n
*N-commut = {!!}

length-+L-distrib : {A : Set} -> (xs ys : List A) -> length (xs +L ys) == length xs +N length ys
length-+L-distrib = {!!}

vecToList : {A : Set} {n : Nat} -> Vec A n -> List A
vecToList = ?

vecToList-listToVec-id : {A : Set} -> (xs : List A) -> vecToList (snd (listToVec xs)) == xs
vecToList-listToVec-id = ?

vTake : {A : Set} {m n : Nat} -> n <= m -> Vec A m -> Vec A n
vTake = ?

-- you need to have implemented <=-refl before this
vTake-id : {A : Set} (n : Nat) (v : Vec A n) -> vTake (<=-refl n) v == v
vTake-id = ?

-- naively reverse a list, by appending at the end
reverse : {A : Set} -> List A -> List A
reverse = {!!}

_ : reverse (1 ,- 2 ,- 3 ,- []) == 3 ,- 2 ,- 1 ,- []
_ = refl _

-- might need +L-assoc here
reverse-+L-distrib : {A : Set} (xs ys : List A) -> reverse (xs +L ys) == reverse ys +L reverse xs
reverse-+L-distrib = {!!}

-- might need reverse-+L-distrib here
reverse-involut : {A : Set} (xs : List A) -> reverse (reverse xs) == xs
reverse-involut = {!!}

-- helper for the linear reverse
-- accumulates the elements of first list, one by one, at the front of the second
-- like how we traditionally implement a linear reverse
-- see the examples below
go : {A : Set} -> List A -> List A -> List A
go = {!!}

_ : go (1 ,- 2 ,- []) [] == 2 ,- 1 ,- []
_ = refl _

_ : go (1 ,- 2 ,- []) (4 ,- 5 ,- []) == 2 ,- 1 ,- 4 ,- 5 ,- []
_ = refl _

-- implement an O(n) reverse by using go
linear-reverse : {A : Set} -> List A -> List A
linear-reverse = {!!}

-- a lemma that will be useful for proving that linear-reverse acts the same as reverse
go-reverse : {A : Set} (xs ys : List A) -> go xs ys == reverse xs +L ys
go-reverse = {!!}

linear-reverse-is-reverse : {A : Set} (xs : List A) -> linear-reverse xs == reverse xs
linear-reverse-is-reverse = {!!}

map : {A B : Set} -> (A -> B) -> List A -> List B
map = {!!}

map-+L-distrib : {A B : Set} -> (f : A -> B) -> (xs ys : List A) -> map f (xs +L ys) == map f xs +L map f ys
map-+L-distrib = {!!}

id : {A : Set} -> A -> A
id x = x

map-id : {A : Set} (xs : List A) -> map id xs == xs
map-id = {!!}

_<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f << g) x = f (g x)

map-compose : {A B C : Set} -> (f : B -> C) (g : A -> B) -> (xs : List A) -> map (f << g) xs == map f (map g xs)
map-compose = {!!}

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr = {!!}

foldr-+L :
  {A B : Set}
  (f : A -> B -> B)
  (xs ys : List A)
  (v : B) ->
  foldr f (foldr f v ys) xs == foldr f v (xs +L ys)
foldr-+L = {!!}

map-foldr :
  {A B : Set}
  (f : A -> B)
  (xs : List A) ->
  map f xs == foldr (\x r -> f x ,- r) [] xs
map-foldr = {!!}

-- uh.. do trees?

-- good example to show how rewrite is implemented, maybe
-- but don't make students solve this
-- listToVec-vecToList-id : {A : Set} {n : Nat} -> (v : Vec A n) -> listToVec (vecToList v) == n , v
-- listToVec-vecToList-id = ?
-}
