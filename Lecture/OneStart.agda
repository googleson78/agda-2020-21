{-# OPTIONS --no-unicode #-}

module OneStart where

data Zero : Set where

-- data Zero
-- f :: forall a. Zero -> a

-- zero == naught
-- E ==  elim
-- naughtE {A} zero
naughtE : {A : Set} -> Zero -> A
naughtE ()

record One : Set where
  constructor <>

data Two : Set where
  ff tt : Two

-- count of members is sum of both
-- disjoint union
-- data Either a b = Left a | Right b
-- |A + B| == |A| + |B|
--  class sum { sum(A); sum(B)};
data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

infixr 8 _+_

-- swap :: Either a b -> Either b a
-- <SPC> m c -- c case split
-- <SPC> m -> ctrl+c
-- ctrl+c ctrl+c
-- A || B -> B || A
+-swap : {A B : Set} -> A + B -> B + A
+-swap (inl x) = inr x
+-swap (inr x) = inl x

-- count of members is product of both
-- cartesian product
-- |A * B| == |A| * |B|
-- class tuple { int fst; int snd;};
record _*_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
-- (a , b)
-- a * b

-- <SPC> m r - refine - introduce constructor
_ : One * Two
_ = <> , tt

infixr 9 _*_

open _*_ public

*-swap : {A B : Set} -> A * B -> B * A
*-swap (fst , snd) = snd , fst

data Nat : Set where
  zero : Nat -- zero
  suc : Nat -> Nat -- 1+

_ : Nat
_ = zero

_ : Nat
_ = suc (suc (suc zero))

{-# BUILTIN NATURAL Nat #-}

-- haskell Integer
_ : Nat
_ = 4 -- suc (suc (suc (suc zero)))

-- <SPC> m r -- place function and make holes for args
_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)
-- (1 + n) + m ==
-- 1 + (n + m)

-- 2 +N 3
-- suc (suc zero) +N 3 -- second case
-- suc (suc zero +N 3) -- second case
-- suc (suc (zero +N 3)) -- first case
-- suc (suc 3)
-- 5

infixr 15 _+N_


-- drinktypes example for type indices
-- and alcohol content dep ret type
data DrinkType : Set where
  milk : DrinkType
  beer : DrinkType

-- data _+_ (A B : Set) : Set where
--   inl : A -> A + B
--   inr : B -> A + B
data Drink : DrinkType -> Set where
  верея : Drink milk
  ariana : Drink beer
  duvel : Drink beer

-- data Vector (A : Set) : Nat -> Set where
--   [] : Vector A zero
--   _,-_ : {n : Nat} -> A -> Vector A n -> Vector A (suc n)

Alcohol : DrinkType -> Set
Alcohol beer = Nat -- колко алкохол има, като число
Alcohol milk = One -- само една възможност, която означава "няма алкохол"

-- Alcohol dt ,,,, drink : Drink dt
-- drink ~ ariana
-- ariana : Drink beer
-- dt ~ beer
-- Alcohol beer ~ Nat

-- Alcohol dt ,,,, drink : Drink dt
-- drink ~ верея
-- верея : Drink milk
-- dt ~ milk
-- Alcohol milk ~ One
alcohol : {dt : DrinkType} -> Drink dt -> Alcohol dt
alcohol ariana = 0
alcohol duvel = 10
alcohol верея = <>


-- json/javascript
-- null
-- число
-- printAlco : (dt : DrinkType) -> Alcohol dt -> IO
-- printAlco milk x = {!!}
-- printAlco beer x = {!!}

-- TwoEq : Two -> Two -> Set
-- TwoEq ff ff = One
-- TwoEq ff tt = Zero
-- TwoEq tt ff = Zero
-- TwoEq tt tt = One
--
-- NatEq : Nat -> Nat -> Set
-- NatEq zero zero = One
-- NatEq zero (suc m) = Zero -- 0 == 1 + ???
-- NatEq (suc n) zero = Zero
-- NatEq (suc n) (suc m) = NatEq n m -- (1 + n) == (1 + m)

data _==_ {A : Set} : A -> A -> Set where
  refl : (x : A) -> x == x

infix 10 _==_

_ : zero == zero
_ = refl zero

-- zero == suc zero
-- refl : (x : A) -> x == x
-- zero /~ suc zero
zeroIsNotOne : zero == suc zero -> Zero
zeroIsNotOne ()

-- how much does agda calculate? examples:
-- 2 +N 2
-- suc (suc zero) +N 2
-- suc (suc (suc (suc zero)))
-- 4
-- p : n == 2
-- p ~ refl 2
-- refl : (x : Nat) -> x == x
-- refl 2 : 2 == 2
-- n == 2
-- 2 == 2
-- n ~ 2
bla : {n : Nat} -> n == 2 -> n +N 2 == 4
bla (refl _) = refl 4

+N-left-zero : (n : Nat) -> zero +N n == n
+N-left-zero n = refl n

-- stuckness explanation
-- ap time

-- n ~ m
-- suc n ~ suc m
-- функционалност
ap : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
ap f (refl x) = refl (f x)

-- n ~ suc n'
-- n +N 0 == n
-- suc n' +N 0 == suc n' --
-- suc (n' +N 0) == suc n'
-- <SPC> m .
-- <SPC> m ,
+N-right-zero : (n : Nat) -> n +N 0 == n
+N-right-zero zero = refl zero
+N-right-zero (suc n') = ap suc (+N-right-zero n')

-- Goal: suc (n' +N 0) == suc n'
-- Have:      n' +N 0  ==     n'
{-

+N-assoc : (n m k : Nat) -> (n +N m) +N k == n +N (m +N k)
+N-assoc n m k = {!!}

-- STUDENTS TIME
+-assoc : {A B C : Set} -> A + (B + C) -> (A + B) + C
+-assoc = {!!}

*-assoc : {A B C : Set} -> A * (B * C) -> (A * B) * C
*-assoc = {!!}

*-distrib-+ : {A B C : Set} -> A * (B + C) -> A * B + A * C
*-distrib-+ = {!!}

+N-right-suc : (n m : Nat) -> suc (n +N m) == n +N suc m
+N-right-suc = {!!}

==-symm : {X : Set} {x y : X} -> x == y -> y == x
==-symm = {!!}

==-trans : {X : Set} {x y z : X} -> x == y -> y == z -> x == z
==-trans = {!!}

-- you'll need ==-symm, ==-trans, +N-right-zero and +N-right-suc here
+N-commut : (n m : Nat) -> n +N m == m +N n
+N-commut = {!!}

data List (a : Set) : Set where
  [] : List a
  _,-_ : a -> List a -> List a

infixr 11 _,-_

-- concatenate two lists
_+L_ : {A : Set} -> List A -> List A -> List A
xs +L ys = {!!}

_ : (3 ,- 5 ,- []) +L  (4 ,- 2 ,- []) == 3 ,- 5 ,- 4 ,- 2 ,- []
_ = refl _

_ : (<> ,- []) +L  (<> ,- []) == <> ,- <> ,- []
_ = refl _

infixr 12 _+L_

+L-assoc : {A : Set} (xs ys zs : List A) -> (xs +L ys) +L zs == xs +L ys +L zs
+L-assoc xs ys zs = {!!}

+L-right-id : {A : Set} (xs : List A) -> xs +L [] == xs
+L-right-id = {!!}

-- calculate the length of a list
length : {A : Set} -> List A -> Nat
length = {!!}

_ : length (<> ,- []) == 1
_ = refl _

_ : length (3 ,- 5 ,- []) == 2
_ = refl _

-- create a list of only the given element, with length the given Nat
replicate : {A : Set} -> Nat -> A -> List A
replicate = {!!}

_ : replicate 2 <> == <> ,- <> ,- []
_ = refl _

_ : replicate 3 5 == 5 ,- 5 ,- 5 ,- []
_ = refl _

-- prove that the length of the replicated list is the original input number to replicate
length-replicate : {A : Set} {x : A} (n : Nat) -> length (replicate n x) == n
length-replicate = {!!}

-- define All to calculate the type which that is inhabited when
-- P is true for all the elements of the given list
All : {X : Set} (P : X -> Set) -> List X -> Set
All = {!!}

-- prove that all of the elements of the result of replicate
-- are the same as the original element given to replicate
replicate-all-==-orig : {A : Set} {x : A} (n : Nat) -> All (_== x) (replicate n x)
replicate-all-==-orig = {!!}
-- this actually isn't necessary thanks to parametricity, but anyway

-}
