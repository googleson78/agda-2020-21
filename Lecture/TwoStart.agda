{-# OPTIONS --no-unicode #-}

module TwoStart where

data Zero : Set where

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

data Nat : Set where
  zero : Nat -- zero
  suc : Nat -> Nat -- 1+

_ : Nat
_ = zero

_ : Nat
_ = suc (suc (suc zero))

{-# BUILTIN NATURAL Nat #-}

_ : Nat
_ = 4 -- suc (suc (suc (suc zero)))

_+N_ : Nat -> Nat -> Nat
zero +N m = m
suc n +N m = suc (n +N m)

infixr 15 _+N_

data _==_ {A : Set} : A -> A -> Set where
  refl : (x : A) -> x == x

infix 10 _==_

_ : zero == zero
_ = refl zero

zeroIsNotOne : zero == suc zero -> Zero
zeroIsNotOne ()

+N-left-zero : (n : Nat) -> zero +N n == n
+N-left-zero n = refl n

ap : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
ap f (refl x) = refl (f x)

+N-right-zero : (n : Nat) -> n +N 0 == n
+N-right-zero zero = refl zero
+N-right-zero (suc n') = ap suc (+N-right-zero n')

-- TODO: mention cheatsheet

-- TODO: mention extra set theoretic explanation of pi and sigma?

-- TODO: mention different meanings of _
-- mixfix
-- figure it out
-- ignored arg
-- TODO: mention project binomial heaps

-- TODO: show "stuckness reasoning" again
+N-assoc : (n m k : Nat) -> (n +N m) +N k == n +N (m +N k)
+N-assoc n m k = {!!}

Even : Nat -> Set
Even = {!!}

Odd : Nat -> Set
Odd = {!!}

data Even' : Nat -> Set where

data Odd' : Nat -> Set where

sucEvenIsOdd : (n : Nat) -> Even n -> Odd (suc n)
sucEvenIsOdd = {!!}

sucEven'IsOdd' : (n : Nat) -> Even' n -> Odd' (suc n)
sucEven'IsOdd' = {!!}

double : Nat -> Nat
double = {!!}

doubleIsEven : (n : Nat) -> Even (double n)
doubleIsEven = {!!}

record _*_ (A : Set) (B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

-- sigma
--record _><_ ??? : Set where
--
--open _><_ public
-- infixr 8 _><_

-- _*_ : Set -> Set -> Set
-- A * B = {!!}
-- infixr 9 _*_

data _<=_ : Nat -> Nat -> Set where

infix 9 _<=_

<=-trans : {n m k : Nat} -> n <= m -> m <= k -> n <= k
<=-trans = {!!}

{-
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

-- correct division by 2
-- you can't divide odd numbers
-- and you also always get back a number that is twice as small as your original one
div2 : (n : Nat) -> Even n -> Nat >< \m -> double m == n
div2 = {!!}

-- every natural number is either Even or Odd
decEvenOrOdd : (n : Nat) -> Even n + Odd n
decEvenOrOdd = {!!}

-- every natural number is either Even' or Odd'
decEven'OrOdd' : (n : Nat) -> Even' n + Odd' n
decEven'OrOdd' = {!!}

<=-refl : (n : Nat) -> n <= n
<=-refl = {!!}

<=-antisym : {n m : Nat} -> n <= m -> m <= n -> n == m
<=-antisym = {!!}

<=-mono-left-+ : {n m : Nat} (k : Nat) -> n <= m -> k +N n <= k +N m
<=-mono-left-+ = {!!}

-- you might need a lemma here
<=-mono-right-+ : {n m : Nat} (k : Nat) -> n <= m -> n +N k <= m +N k
<=-mono-right-+ = {!!}

-- use with!
<=-total : (n m : Nat) -> n <= m + m <= n
<=-total = {!!}

-- multiplication using repeated addition
_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N n *N m
infixr 40 _*N_

-- EXERCISE: multiplication right identity
*N-right-id : (n : Nat) -> n *N 1 == n
*N-right-id = {!!}

-- EQUATIONAL REASONING UTILS
-- YOU CAN USE THESE FOR *N TASKS, BUT THEY ARE NOT MANDATORY
-- IF YOU WANT TO USE THEM FOR THIS PURPOSSE, SEE THE EXAMPLE AT THE END OF THE UTILS CODE BLOCK
-- LIKELY BETTER TO IGNORE THEIR IMPLEMENTATIONS FOR NOW
_=[]_ : {A : Set} {y : A} -> (x : A) -> x == y -> x == y
x =[] (refl _) = refl _

infixr 1 _=[]_

_=[_]_ : {A : Set} {y z : A} -> (x : A) -> x == y -> y == z -> x == z
x =[ refl _ ] (refl _) = refl _

infixr 1 _=[_]_

_QED : {A : Set} -> (x : A) -> x == x
x QED = refl x

infix 3 _QED
-- END OF UTILS

-- +N-commut, but  demonstrated with equational reasoning utils
+N-commut' : (n m : Nat) -> n +N m == m +N n
+N-commut' zero m =
  m
    =[ ==-symm (+N-right-zero m) ]
  m +N zero
    QED
+N-commut' (suc n) m =
  suc (n +N m)
    =[ ap suc (+N-commut' n m) ]
  suc (m +N n)
    =[ +N-right-suc m n ]
  m +N suc n
    QED

-- multiplication distributes over addition
*N-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
*N-distrib-+N = {!!}

-- use *N-distrib-+N
*N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
*N-assoc = {!!}

-- figure out what lemmas you need
*N-commut : (n m : Nat) -> n *N m == m *N n
*N-commut = {!!}

-}
