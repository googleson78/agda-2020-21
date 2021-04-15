{-# OPTIONS --no-unicode #-}

module Lecture.FourStart where

open import Lib.List
open import Lib.Vec
open import Lib.Eq
open import Lib.Nat
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Sigma

-- describe modules
-- show example with open

module Listy (A : Set) where
  x : Nat
  x = zero

  id' : A -> A
  id' y = y

  bla : Nat -> Set
  bla n = A

-- z : Nat
-- z = {!id'!}

-- show bst constructions
-- write Bound
-- write LeqBound
-- write BST
-- explain "pushing down constraints"
-- examples for bst
-- show tree diagram

LeqNat : Nat -> Nat -> Set
LeqNat zero m = One
LeqNat (suc n) zero = Zero
LeqNat (suc n) (suc m) = LeqNat n m

_ : 3 <= 5
_ = osuc (osuc (osuc ozero))

_ : LeqNat 3 5
_ = <>

decLeqNat : (n m : Nat) -> LeqNat n m + LeqNat m n
decLeqNat zero zero = inl <>
decLeqNat zero (suc m) = inl <>
decLeqNat (suc n) zero = inr <>
decLeqNat (suc n) (suc m) = decLeqNat n m

<=-LeqNat : {n m : Nat} -> n <= m -> LeqNat n m
<=-LeqNat p = {!!}

module
  Sorting
    (Key : Set)
    (Leq : Key -> Key -> Set)
    (_<=?_ : (x y : Key) -> Leq x y + Leq y x)
  where

  data Bound : Set where
    -inf : Bound
    inKey : Key -> Bound
    +inf : Bound

  LeqBound : Bound -> Bound -> Set
  LeqBound -inf y = One
  LeqBound x +inf = One
  LeqBound (inKey x) (inKey y) = Leq x y
  LeqBound _ _ = Zero

  data BST (lo hi : Bound) : Set where
    empty : LeqBound lo hi -> BST lo hi

    node :
      (k : Key) ->
      (left : BST lo (inKey k)) ->
      (right : BST (inKey k) hi) ->
      BST lo hi

  -- you can use _<=?_ to compare two values
  insert :
    {lo hi : Bound} (k : Key) ->
    LeqBound lo (inKey k) -> LeqBound (inKey k) hi ->
    BST lo hi -> BST lo hi
  insert = {!!}

  makeTree : List Key -> BST -inf +inf
  makeTree = {!!}

  -- use the same idea as in BST to define "ordered lists"
  -- be careful about what constraints you need in your recursive case!
  data OList (lo hi : Bound) : Set where

  -- append ordered lists
  -- note that we require a key to "bridge" the two lists
  -- try to implement
  -- append : {lo mid hi : Bound} -> OList lo mid -> OList mid hi -> OList lo hi
  -- and see where you get stuck
  appendKeyed : {lo hi : Bound} -> (k : Key) -> OList lo (inKey k) -> OList (inKey k) hi -> OList lo hi
  appendKeyed = {!!}

  flatten : {lo hi : Bound} -> BST lo hi -> OList lo hi
  flatten = {!!}

  sort : List Key -> OList -inf +inf
  sort xs = flatten (makeTree xs)

--          2
--       1  .  3
--     <=.<=.<=.<=
--       .  .  .
-- -inf<=1<=2<=3<=+inf

open Sorting Nat LeqNat decLeqNat

one : BST -inf (inKey 2)
one = node 1 (empty <>) (empty <>)

three : BST (inKey 2) +inf
three = node 3 (empty <>) (empty <>)

two : BST -inf +inf
two = node 2 one three

Dec : (A : Set) -> Set
Dec A = (A -> Zero) + A

-- TODO:
-- grey highlight

-- plusnat : Nat -> Nat -> Nat
-- plusnat zero m = m
-- plusnat n zero = n
-- plusnat (suc n) m = suc (plusnat n m)
--
-- f : (m : Nat) -> plusnat zero m == m
-- f m = refl
--
-- g : (m : Nat) -> plusnat m zero == m
-- g zero = {!!}
-- g (suc m) = {!!}

-- case n of
--   zero -> m
--   suc n ->
--     case m of
--       zero -> n
--       ...

-- plusnat n m == plusnat m n // n -> zero
-- plusnat zero m -> m
-- Goal: m == plusnat m zero
-- m == m
-- plusnat-commut : (n m : Nat) -> plusnat n m == plusnat m n
-- plusnat-commut zero m = {!!}
-- plusnat-commut (suc n) m = {!!}

-- "pipe"s in goal
-- with generalises (show vs lambda)
-- show generalised:
-- goal type

-- original args
-- other later withs
--
-- dots ??

-- asd : Nat -> Nat
-- asd n with decLeqNat n 5
-- ... | inl x = 5
-- ... | inr x = n
--
-- pasd : (n : Nat) -> LeqNat 5 n -> asd n == n
-- pasd n x with decLeqNat n 5
-- ... | inl x1 = {!!}
-- ... | inr x1 = {!!}


-- bla : (n : Nat) -> n == 10 -> 0 == n
-- bla n x with n
-- ... | z = {!z!}
--
-- bla2 : (n : Nat) -> 0 == n
-- bla2 n with n
-- bla2 n | zero with 5
-- bla2 n | zero | q = {!!}
-- bla2 n | suc z = {!!}

-- pasd : (n : Nat) -> 6 <= n -> asd n == n
-- pasd = {!!}

-- +N-right-zero' : (n : Nat) -> n +N 0 == n
-- +N-right-zero' zero = refl
-- -- +N-right-zero' (suc n) rewrite +N-right-zero' n = refl
-- +N-right-zero' (suc n) with n +N 0 with +N-right-zero' n
-- ... | .n | refl = refl

-- Goal: suc (n +N 0) == suc n
-- ————————————————————————————————————————————————————————————
-- z : n +N 0 == n
-- n : Nat
-- after
-- Goal: suc u == suc n
-- ————————————————————————————————————————————————————————————
-- z : u == n
-- u : Nat
-- n : Nat

{-

-- used a module to introduce global vars
-- in here, you can compare values for equality with _==?_
-- in all proofs for functions defined with a `with`
-- you're most likely going to need to do another with
-- because your proof will be stuck on the result of the with in the original function def
module listy {A : Set} {_==?_ : (x y : A) -> Dec (x == y)} where

  infix 10 _In_

  data _In_ (x : A) : List A -> Set where
    here : {xs : List A} -> x In (x ,- xs)
    there : {y : A} {xs : List A} -> x In xs -> x In (y ,- xs)

  +L-monoL-In : {y : A} {ys : List A} -> (xs : List A) -> y In ys -> y In xs +L ys
  +L-monoL-In = {!!}

  +L-splits-In : {x : A} (xs ys : List A) -> x In xs +L ys -> x In xs + x In ys
  +L-splits-In = {!!}

  notIn[] : {x : A} -> x In [] -> Zero
  notIn[] = {!!}

  nowhere : {x y : A} {ys : List A} -> (x == y -> Zero) -> (x In ys -> Zero) -> x In y ,- ys -> Zero
  nowhere = {!!}

  -- if there is one, return the first x in the list
  find : (x : A) (xs : List A) -> Dec (x In xs)
  find = {!!}

  -- delete all the occurrences of x in the list
  remove : (x : A) -> (xs : List A) -> List A
  remove = {!!}

  remove-removes : (xs : List A) -> (x : A) -> x In remove x xs -> Zero
  remove-removes = {!!}

  remove-keeps : (xs : List A) (y : A) -> y In xs -> (x : A) -> (x == y -> Zero) -> y In remove x xs
  remove-keeps = {!!}

  -- xs Sub ys - xs is a subsequence of ys
  -- [] Sub []
  -- 5 ,- [] Sub 5 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 5 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 5 ,- 4 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 4 ,- 5 ,- []
  data _Sub_ : List A -> List A -> Set where
    s[] : [] Sub []
    s-cons : {x : A} {xs ys : List A} -> xs Sub ys -> (x ,- xs) Sub (x ,- ys)
    s-skip : {x : A} {xs ys : List A} -> xs Sub ys -> xs Sub (x ,- ys)

  infix 10 _Sub_

  s[]-all : (xs : List A) -> [] Sub xs
  s[]-all = {!!}

  Sub-refl : (xs : List A) -> xs Sub xs
  Sub-refl = {!!}

  -- try to make the definition "as lazy" as possible - meaning pattern matching on as few things as possible
  -- this will affect your proof for Sub-trans-assoc
  Sub-trans : {xs ys zs : List A} -> xs Sub ys -> ys Sub zs -> xs Sub zs
  Sub-trans = {!!}

  +L-monoL-Sub : (xs ys : List A) -> xs Sub (xs +L ys)
  +L-monoL-Sub = {!!}

  +L-monoR-Sub : (xs ys : List A) -> xs Sub (ys +L xs)
  +L-monoR-Sub = {!!}

  Sub-all-In : {xs ys : List A} -> xs Sub ys -> {x : A} -> x In xs -> x In ys
  Sub-all-In = {!!}

  remove-Sub : (x : A) (xs : List A) -> remove x xs Sub xs
  remove-Sub = {!!}

  -- might need to make an implicit arg explicit in one of the cases
  remove-preserves-Sub : {xs ys : List A} (x : A) -> xs Sub ys -> remove x xs Sub ys
  remove-preserves-Sub = {!!}

  ,-Sub-remove : {xs ys : List A} (x : A) -> xs Sub x ,- ys -> remove x xs Sub ys
  ,-Sub-remove = {!!}

  Sub-trans-assoc :
    {xs ys zs vs : List A} (sub1 : xs Sub ys) (sub2 : ys Sub zs) (sub3 : zs Sub vs) ->
    Sub-trans (Sub-trans sub1 sub2) sub3 == Sub-trans sub1 (Sub-trans sub2 sub3)
  Sub-trans-assoc = {!!}

decNatEq : (n m : Nat) -> Dec (n == m)
decNatEq = ?


open listy {Nat} {decNatEq}

_ : 3 In 3 ,- 5 ,- []
_ = here

_ : 5 In 3 ,- 5 ,- []
_ = there here

5notIn[] : 5 In [] -> Zero
5notIn[] ()

5notIn3 : 5 In 3 ,- [] -> Zero
5notIn3 (there ())

_ : [] Sub []
_ = s[]

_ : 5 ,- [] Sub 5 ,- []
_ = s-cons s[]

_ : 3 ,- 5 ,- [] Sub 3 ,- 5 ,- []
_ = s-cons (s-cons s[])

_ : 3 ,- 5 ,- [] Sub 3 ,- 5 ,- 4 ,- []
_ = s-cons (s-cons (s-skip s[]))

_ : 3 ,- 5 ,- [] Sub 3 ,- 4 ,- 5 ,- []
_ = s-cons (s-skip (s-cons s[]))

32notSub23 : 3 ,- 2 ,- [] Sub 2 ,- 3 ,- [] -> Zero
32notSub23 (s-skip (s-cons ()))
32notSub23 (s-skip (s-skip ()))

332notSub32 : 3 ,- 3 ,- 2 ,- [] Sub 3 ,- 2 ,- [] -> Zero
332notSub32 (listy.s-cons (listy.s-skip ()))
332notSub32 (listy.s-skip (listy.s-skip ()))

-- implement less than or equal for nats, but in a different way
-- look at _Sub_ and think how to "strip away" all the information Lists have compared to Nats
-- the S is because it's similar to Sub, and because I need another name
-- (also for "selection" I guess)
data _<S=_ : Nat -> Nat -> Set where
  o-zero : {!!} <S= {!!}
  o-skip : {n m : Nat} -> {!!}
  o-succ : {n m : Nat} -> {!!}

_ : 1 <S= 1
_ = {!!}

_ : 1 <S= 3
_ = {!!}

_ : 3 <S= 5
_ = {!!}

-- in general there's more than one way in which n <S= m!
-- find out all the ways

_ :
  (1 <S= 2) >< \p -> -- there's a proof p for 1 <S= 2
  (1 <S= 2) >< \q -> -- and a proof q for 1 <S= 2
  p == q -> Zero     -- and they're different
_ = {!!}

-- it might be interesting to try to figure out how many proofs there are for n <S= m, for fixed n and m
-- you can use -l in a hole for such a proof (e.g. 1 <S= 4), together with agdas auto, to get it to list all of them


-- we can have an "empty" sub - it selects nothing
-- this makes more sense once you reach select - so if you want to you can read the comment on select first
-- alternatively you can think of it as "just a proof"
0<S= : (n : Nat) -> 0 <S= n
0<S= = {!!}

-- similarly, we can have an "all" sub - it selects everything
-- or alternatively, a reflexivity proof
refl-<S= : (n : Nat) -> n <S= n
refl-<S= = {!!}

-- there is only one empty sub (and only one proof) - and that's the one you wrote
0<S=-unique : {n : Nat} (p : 0 <S= n) -> 0<S= n == p
0<S=-unique = {!!}

-- we can construct a sub from our usual leq
<=-<S= : {n m : Nat} -> n <= m -> n <S= m
<=-<S= = {!!}

-- and vice versa
-- you might need <=-trans here and an additonal lemma for one of the cases
<S=-<= : {n m : Nat} -> n <S= m -> n <= m
<S=-<= = {!!}


-- we can use <S= to encode a "choice of elements" from a vector
-- this is similar in purpose to _Sub_
-- but uses less information than _Sub_, which potentially carries around lists as its arguments (look in the constructors) as we only store Nats
--
-- use the <S= proof to guide you on when to keep an element and when to drop one
select : {A : Set} {m n : Nat} -> n <S= m -> Vec A m -> Vec A n
select = {!!}


-- we can compose selections
-- alternatively, this is transitivity for <S=
-- make this as lazy as possible in its pattern matches (so as few matches as possible)
-- so that your later proofs are also easier!
-- hint: match on the right one first
_S<<_ : {n m k : Nat} -> n <S= m -> m <S= k -> n <S= k
p S<< q = {!!}

-- selecting a composition is the same as composing selects
-- it doesn't matter if we select a composition or select twice
-- (or in other words, it doesn't matter whether compose first or select first)
select-S<< :
  {A : Set} {n m k : Nat}
  (p : n <S= m) (q : m <S= k) (xs : Vec A k) ->
  select (p S<< q) xs == select p (select q xs)
select-S<< = {!!}

-- it doesn't matter if we compose with the id selection on the left
S<<-left-id : {n m : Nat} (p : n <S= m) -> (refl-<S= n S<< p) == p
S<<-left-id = {!!}

-- or on the right
S<<-right-id : {n m : Nat} (p : n <S= m) -> (p S<< (refl-<S= m)) == p
S<<-right-id = {!!}


-- and it's also associative
S<<-assoc :
  {n m k v : Nat} (p : n <S= m) (q : m <S= k) (t : k <S= v) ->
  (p S<< q) S<< t == p S<< (q S<< t)
S<<-assoc = {!!}

-- we can use selections of a particular form to index into a vector
-- a selection with 1 on the left effectively means that there is only one place in its construction that can have a o-succ constructor
-- that's *exactly* the index of the item we want to get from the vector
-- (use select and vHead)
vProject : {A : Set} {n : Nat} -> Vec A n -> 1 <S= n -> A
vProject = {!!}

-- note the locations of the "up arrows"

_ : vProject (0 ,- 1 ,- 2 ,- []) (o-succ (o-skip (o-skip o-zero))) == 0
--            ^                   ^
_ = refl

_ : vProject (0 ,- 1 ,- 2 ,- []) (o-skip (o-succ (o-skip o-zero))) == 1
--                 ^                      ^
_ = refl

_ : vProject (0 ,- 1 ,- 2 ,- []) (o-skip (o-skip (o-succ o-zero))) == 2
--                      ^                         ^
_ = refl

-- but we can also do the opposite!
-- if we can get a value for every 1 <S= n, then we effectively know all the elements of a vector
vTabulate : {A : Set} (n : Nat) -> (1 <S= n -> A) -> Vec A n
vTabulate = {!!}

-- tabulating projections should result in the original vector
-- "evaluate more pls agda" might be useful here
-- reminder:
-- spacemacs - <SPC> u <SPC> u <normal-bind>
-- vscode - (should be) C-u C-u <normal-bind>
vTabulate-vProject : {A : Set} {n : Nat} -> (xs : Vec A n) -> vTabulate n (vProject xs) == xs
vTabulate-vProject = {!!}

-- projecting a tabulation should result in the original tabulation
-- again, "evaluate more pls" might be useful
-- uniqueness for 0<S= might also be useful
vProject-vTabulate :
  {A : Set} {n : Nat}
  (f : 1 <S= n -> A) (i : 1 <S= n) ->
  vProject (vTabulate n f) i == f i
vProject-vTabulate = {!!}

-}
