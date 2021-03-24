{-# OPTIONS --no-unicode #-}

module Lecture.ThreeStart where

open import Lib.Nat
open import Lib.Eq
open import Lib.List
open import Lib.One
open import Lib.Zero
open import Lib.Two
open import Lib.Sum
open import Lib.Sigma

-- !show rewrite

-- maybe send link on actual rewrite
+N-right-zero' : (n : Nat) -> n +N 0 == n
+N-right-zero' zero = refl
+N-right-zero' (suc n) rewrite +N-right-zero' n = refl

-- rewrite allows us to replace "by an equality"

-- +N-right-zero' n : n +N 0 == n
-- suc (n +N 0) == suc n

-- 3 + n
-- n == m
-- 3 + m


-- James McKinna, Conor McBride
-- !show with
-- !don't forget to say what the three dots mean!!
-- !demonstrate that when we match, goal changes
-- !show lambda
-- !?show where
-- !?show "generate helper"
-- decide

-- refl
-- suc n == suc m
-- suc n == suc n
-- n ~ m
not-eq-suc : {n m : Nat} -> (n == m -> Zero) -> suc n == suc m -> Zero
not-eq-suc notn==m refl = notn==m refl

-- (\ x y z -> x + y + z) 1 2 3 == 6
dec== : (n m : Nat) -> n == m + (n == m -> Zero)
dec== zero zero = inl refl
dec== zero (suc m) = inr \() -- refine, <SPC> m r
dec== (suc n) zero = inr \()
dec== (suc n) (suc m) with dec== n m
dec== (suc n) (suc .n) | inl refl = inl refl
dec== (suc n) (suc m) | inr notp = inr (not-eq-suc notp)
-- <SPC> m h
-- with abstraction
-- unordered_map<T, bool>

--  where
--  helper :
--    {n m : Nat} ->
--    n == m + (n == m -> Zero) ->
--    suc n == suc m + (suc n == suc m -> Zero)
--  helper (inl p) = inl (ap suc p)
--  helper (inr notp) = inr \ q -> not-eq-suc notp q

_ : 3 == 2 + (3 == 2 -> Zero)
_ = dec== 3 2

bla : (n : Nat) -> n == 2 -> 2 +N n == 4
bla .2 refl = refl

-- case dec== n 2 of
--   inl p -> bla n p
--   inr notp -> putStrLn "invalid input"

Even : Nat -> Set
Even zero = One
Even (suc zero) = Zero -- 1
Even (suc (suc n)) = Even n -- 2 + n

-- !explain how this is an "exists"
-- !examples!
-- !do these on another "live solving session" instead:
-- show how this generalises _+_ ?
-- and how (a : A) -> P a generalises _*_ ?
-- record _><_ (A : Set) (P : A -> Set) : Set where
--   constructor _,_
--
--   field
--     fst : A
--     snd : P fst

-- record Customer
--   field
--     age : Int
--     alcohol : if age > 18 then List Drink else One

-- data Sg (A : Set) (P : A -> Set) : Set where
--   sg : (fst : A) -> P fst -> Sg A P

-- open _><_ public
--
-- infixr 8 _><_

_ : Nat >< \n -> Nat >< \m -> n == m
_ = zero , (zero , refl)

-- (a : A) -> ...
-- ∀(a ∈ A).  ...
-- ∃(n ∈ Nat). Even n
_ : Nat >< \n -> Even n
_ = 2 , <>

-- _*_ : Set -> Set -> Set
-- A * B = A >< \ _ -> B
-- infixr 9 _*_

_ : Nat * Nat
_ = zero , zero


data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _,-_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)


-- lHead : {A : Set}-> List A -> A
-- lHead [] = {!error "Prelude.head empty list !}
-- lHead (x ,- _) = x

vHead : {A : Set} {n : Nat} -> Vec A (suc n) -> A
vHead (x ,- _) = x


vTail : {A : Set} {n : Nat} -> Vec A (suc n) -> Vec A n
vTail (_ ,- xs) = xs

-- !?show parallel with +L - agda can now write it itself
_+L'_ : {A : Set} -> List A -> List A -> List A
[] +L' ys = ys
(x ,- xs) +L' ys = x ,- (xs +L' ys)

_+V_ : {A : Set} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n +N m)
[] +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)


infixr 12 _+V_

-- readLn :: [Char]
-- input <- readLn
--
-- case listToVec input of
-- zero, [] -> putStLn "invalid input"
-- suc n, v -> isLengthMoreThan10 v n
--
-- 10 <= n

listToVec : {A : Set} -> List A -> Nat >< \ n -> Vec A n
listToVec [] = zero , []
listToVec (x ,- xs) =
  let n , xs' = listToVec xs
  in suc n , (x ,- xs')

_=[]_ : {A : Set} {y : A} -> (x : A) -> x == y -> x == y
x =[] refl = refl

infixr 1 _=[]_

_=[_>=_ : {A : Set} {y z : A} -> (x : A) -> x == y -> y == z -> x == z
x =[ refl >= refl = refl

infixr 1 _=[_>=_

_=<_]=_ : {A : Set} {y z : A} -> (x : A) -> y == z -> x == y -> x == z
x =< refl ]= refl = refl

infixr 1 _=<_]=_

_QED : {A : Set} -> (x : A) -> x == x
x QED = refl

infix 3 _QED

-- n == // защото n е пешо и гошо
-- m == // защото лагранж
-- z QED

-- ! show =[] for zero case?
-- ! show eq reasoning with commut
-- ! maybe write out eq reasoning?

+N-commut' : (n m : Nat) -> n +N m == m +N n
+N-commut' zero m =
  m
    =[ ==-symm (+N-right-zero m) >=
  m +N zero
    QED
+N-commut' (suc n) m =
  suc (n +N m)
    =[ ap suc (+N-commut' n m) >=
  suc (m +N n)
    =[ ==-symm (+N-right-suc m n) >=
  m +N suc n
    QED


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

-- m - n
-- d for difference
difference<= : (m n : Nat) -> n <= m -> Nat >< \d -> m == n +N d
difference<= = {!!}

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

add-two-Even : (n m : Nat) -> Even m -> Even (n +N n +N m)
add-two-Even = {!!}

*N-consecutive-Even : (n : Nat) -> Even (n *N suc n)
*N-consecutive-Even = {!!}

downFrom : Nat -> Nat
downFrom zero = zero
downFrom (suc n) = suc n +N downFrom n

div2 : (n : Nat) -> Even n -> Nat
div2 = {!!}

downFrom-closed-form : (n : Nat) -> 2 *N downFrom n == n *N suc n
downFrom-closed-form = {!!}

-- "abuse" modules so we can have the same name datatype twice
module listsplit where
  -- a "splitting" - a description of how a list was split into two others
  -- alternatively, a description/plan of how to merge two lists to make a third
  data _<[_]>_ {A : Set} : List A -> List A -> List A -> Set where
    -- we can always split the empty list into two other empty lists
    []split : [] <[ [] ]> []

    -- if we can split zs into xs and ys
    -- then we can also simultaneously add an element on the left (to xs) and to zs
    left : {xs ys zs : List A} {x : A} ->
           xs <[      zs ]>      ys ->
      x ,- xs <[ x ,- zs ]>      ys

    -- same as above, but with the right list
    right : {xs ys zs : List A} {x : A} ->
           xs <[      zs ]>      ys ->
           xs <[ x ,- zs ]> x ,- ys

  infix 10 _<[_]>_

  -- for a predicate to be decidable, it must be decidable for every value
  Dec : {A : Set} -> (A -> Set) -> Set
  Dec {A} P = (x : A) -> (P x -> Zero) + P x

  -- given a decidable predicate and a list, produce two lists
  -- one with all the elements for which the predicate holds
  -- and one with all the elements for which it doesn't
  partition :
    {A : Set} {P : A -> Set} -> (Dec P) -> (xs : List A) ->
      List A >< \nays ->
      List A >< \yeas ->
        nays <[ xs ]> yeas *
        All (\x -> P x -> Zero) nays *
        All P yeas
  partition p? xs = {!!}

module natsplit where
  -- same idea as with lists
  data _<[_]>_ : Nat -> Nat -> Nat -> Set where
    zero : zero <[ zero ]> zero

    left : {l r m : Nat} ->
          l <[     m ]>      r ->
      suc l <[ suc m ]>      r

    right : {l r m : Nat} ->
           l <[     m ]>     r ->
           l <[ suc m ]> suc r

  infix 10 _<[_]>_

  -- use the splitting to guide you on how to merge the two vectors
  _>[_]<_ : {A : Set} {l m r : Nat} -> Vec A l -> l <[ m ]> r -> Vec A r -> Vec A m
  xs >[ spl ]< ys = {!!}

  split : {A : Set} (l m r : Nat) (spl : l <[ m ]> r) (xs : Vec A m) ->
    Vec A l >< \lefts ->
    Vec A r >< \rights ->
      (lefts >[ spl ]< rights) == xs
  split l m r spl xs = {!!}
-}
