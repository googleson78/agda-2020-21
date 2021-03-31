{-# OPTIONS --no-unicode #-}

module Lecture.ThreeSolved where

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

_ : 2 == 2
_ = refl

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

-- n == // защото n е пешо и гошо
-- m == // защото лагранж
-- z QED

-- ! show =[] for zero case?
-- ! show eq reasoning with commut
-- ! maybe write out eq reasoning?

+N-commut' : (n m : Nat) -> n +N m == m +N n
+N-commut' zero m =
  m
    =< +N-right-zero m ]=
  m +N zero
    QED
+N-commut' (suc n) m =
  suc (n +N m)
    =[ ap suc (+N-commut' n m) >=
  suc (m +N n)
    =< +N-right-suc m n ]=
  m +N suc n
    QED


<=-refl : (n : Nat) -> n <= n
<=-refl zero = ozero
<=-refl (suc n) = osuc (<=-refl n)

<=-antisym : {n m : Nat} -> n <= m -> m <= n -> n == m
<=-antisym ozero ozero = refl
<=-antisym (osuc n<=m) (osuc m<=n) rewrite <=-antisym n<=m m<=n = refl

<=-mono-left-+N : {n m : Nat} (k : Nat) -> n <= m -> k +N n <= k +N m
<=-mono-left-+N zero p = p
<=-mono-left-+N (suc k) p = osuc (<=-mono-left-+N k p)

-- you might need a lemma here
<=-mono-right-+N : {n m : Nat} (k : Nat) -> n <= m -> n +N k <= m +N k
<=-mono-right-+N {n} {m} k p
  rewrite +N-commut n k
  rewrite +N-commut m k
  = <=-mono-left-+N k p

-- multiplication using repeated addition
_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N n *N m
infixr 40 _*N_

-- EXERCISE: multiplication right identity
*N-right-id : (n : Nat) -> n *N 1 == n
*N-right-id zero = refl
*N-right-id (suc n) rewrite *N-right-id n = refl

-- multiplication distributes over addition
*N-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
*N-distrib-+N zero m k = refl
*N-distrib-+N (suc n) m k =
  k +N (n +N m) *N k
    =[ ap (k +N_) (*N-distrib-+N n m k) >=
  k +N n *N k +N m *N k
    =< +N-assoc k (n *N k) (m *N k) ]=
  (k +N n *N k) +N m *N k
    QED

--  rewrite *N-distrib-+N n m k
--  = ==-symm (+N-assoc k (n *N k) (m *N k))
-- k +N ((n *N k) +N (m *N k)) == (k +N (n *N k)) +N (m *N k)

-- use *N-distrib-+N
*N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
*N-assoc zero m k = refl
*N-assoc (suc n) m k =
  (m +N n *N m) *N k
    =[ *N-distrib-+N m (n *N m) k >=
  m *N k +N (n *N m) *N k --(m +N n *N m) *N k
    =[ ap ((m *N k +N_)) (*N-assoc n m k) >=
  m *N k +N n *N m *N k
    QED

*N-right-zero : (n : Nat) -> zero == n *N zero
*N-right-zero zero = refl
*N-right-zero (suc n) = *N-right-zero n

*N-right-suc : (n m : Nat) -> n +N n *N m == n *N suc m
*N-right-suc zero m = refl
*N-right-suc (suc n) m
  rewrite ==-symm (*N-right-suc n m)
  -- Goal: n +N (m +N (n *N m)) == m +N (n +N (n *N m))
  rewrite ==-symm (+N-assoc n m (n *N m))
  -- Goal: (n +N m) +N n *N m == m +N n +N n *N m
  rewrite +N-commut n m
  -- Goal: (m +N n) +N n *N m == m +N n +N n *N m
  rewrite +N-assoc m n (n *N m)
  = ap suc refl


-- figure out what lemmas you need
*N-commut : (n m : Nat) -> n *N m == m *N n
*N-commut zero m = *N-right-zero m
*N-commut (suc n) m rewrite *N-commut n m = *N-right-suc m n

length-+L-distrib : {A : Set} -> (xs ys : List A) -> length (xs +L ys) == length xs +N length ys
length-+L-distrib [] ys = refl
length-+L-distrib (x ,- xs) ys = ap suc (length-+L-distrib xs ys)

vecToList : {A : Set} {n : Nat} -> Vec A n -> List A
vecToList [] = []
vecToList (x ,- xs) = x ,- vecToList xs

vecToList-listToVec-id : {A : Set} -> (xs : List A) -> vecToList (snd (listToVec xs)) == xs
vecToList-listToVec-id [] = refl
vecToList-listToVec-id (x ,- xs) = ap (x ,-_) (vecToList-listToVec-id xs)

vTake : {A : Set} {m n : Nat} -> n <= m -> Vec A m -> Vec A n
vTake ozero xs = []
vTake (osuc n<=m) (x ,- xs) = x ,- vTake n<=m xs

-- you need to have implemented <=-refl before this
vTake-id : {A : Set} {n : Nat} (v : Vec A n) -> vTake (<=-refl n) v == v
vTake-id [] = refl
vTake-id (x ,- xs) = ap (x ,-_ ) (vTake-id xs)


-- m - n
-- d for difference
difference<= : (m n : Nat) -> n <= m -> Nat >< \d -> m == n +N d
difference<= m zero ozero = m , refl
difference<= (suc m) (suc n) (osuc n<=m) with difference<= m n n<=m
... | d , refl = d , refl

-- naively reverse a list, by appending at the end
reverse : {A : Set} -> List A -> List A
reverse [] = []
reverse (x ,- xs) = reverse xs +L (x ,- [])

_ : reverse (1 ,- 2 ,- 3 ,- []) == 3 ,- 2 ,- 1 ,- []
_ = refl


-- might need +L-assoc here
reverse-+L-distrib : {A : Set} (xs ys : List A) -> reverse (xs +L ys) == reverse ys +L reverse xs
reverse-+L-distrib [] ys rewrite +L-right-id (reverse ys) = refl
reverse-+L-distrib (x ,- xs) ys
  -- reverse (xs +L ys) +L (x ,- []) == reverse ys +L reverse xs +L (x ,- [])
  rewrite reverse-+L-distrib xs ys
  -- (reverse ys +L reverse xs) +L (x ,- []) == reverse ys +L reverse xs +L (x ,- [])
  = +L-assoc (reverse ys) (reverse xs) (x ,- [])

-- might need reverse-+L-distrib here
reverse-involut : {A : Set} (xs : List A) -> reverse (reverse xs) == xs
reverse-involut [] = refl
reverse-involut (x ,- xs)
  rewrite reverse-+L-distrib (reverse xs) (x ,- [])
  = ap (x ,-_) (reverse-involut xs)

-- helper for the linear reverse
-- accumulates the elements of first list, one by one, at the front of the second
-- like how we traditionally implement a linear reverse
-- see the examples below
go : {A : Set} -> List A -> List A -> List A
go [] ys = ys
go (x ,- xs) ys = go xs (x ,- ys)


_ : go (1 ,- 2 ,- []) [] == 2 ,- 1 ,- []
_ = refl

_ : go (1 ,- 2 ,- []) (4 ,- 5 ,- []) == 2 ,- 1 ,- 4 ,- 5 ,- []
_ = refl

-- implement an O(n) reverse by using go
linear-reverse : {A : Set} -> List A -> List A
linear-reverse xs = go xs []

-- a lemma that will be useful for proving that linear-reverse acts the same as reverse
go-reverse : {A : Set} (xs ys : List A) -> go xs ys == reverse xs +L ys
go-reverse [] ys = refl
go-reverse (x ,- xs) ys
  rewrite go-reverse xs (x ,- ys)
  = ==-symm (+L-assoc (reverse xs) (x ,- []) ys)

linear-reverse-is-reverse : {A : Set} (xs : List A) -> linear-reverse xs == reverse xs
linear-reverse-is-reverse [] = refl
linear-reverse-is-reverse (x ,- xs) = go-reverse xs (x ,- [])


map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x ,- xs) = f x ,- map f xs

map-+L-distrib : {A B : Set} -> (f : A -> B) -> (xs ys : List A) -> map f (xs +L ys) == map f xs +L map f ys
map-+L-distrib f [] ys = refl
map-+L-distrib f (x ,- xs) ys = ap (f x ,-_) (map-+L-distrib f xs ys)

id : {A : Set} -> A -> A
id x = x

map-id : {A : Set} (xs : List A) -> map id xs == xs
map-id [] = refl
map-id (x ,- xs) = ap (x ,-_) (map-id xs)

_<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f << g) x = f (g x)

-- theorems for free - philip wadler
map-compose : {A B C : Set} -> (f : B -> C) (g : A -> B) -> (xs : List A) -> map (f << g) xs == map f (map g xs)
map-compose f g [] = refl
map-compose f g (x ,- xs) = ap (f (g x) ,-_) (map-compose f g xs)

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f v [] = v
foldr f v (x ,- xs) = f x (foldr f v xs)

foldr-+L :
  {A B : Set}
  (f : A -> B -> B)
  (xs ys : List A)
  (v : B) ->
  foldr f (foldr f v ys) xs == foldr f v (xs +L ys)
foldr-+L f [] ys v = refl
foldr-+L f (x ,- xs) ys v = ap (f x) (foldr-+L f xs ys v)

map-foldr :
  {A B : Set}
  (f : A -> B)
  (xs : List A) ->
  map f xs == foldr (\x r -> f x ,- r) [] xs
map-foldr f [] = refl
map-foldr f (x ,- xs) = ap (f x ,-_) (map-foldr f xs)


-- uh.. do trees?

-- good example to show how rewrite is implemented, maybe
-- but don't make students solve this
-- listToVec-vecToList-id : {A : Set} {n : Nat} -> (v : Vec A n) -> listToVec (vecToList v) == n , v
-- listToVec-vecToList-id = ?

add-two-Even : (n m : Nat) -> Even m -> Even (n +N n +N m)
add-two-Even zero m p = p
add-two-Even (suc n) m p
  rewrite +N-right-suc n (n +N m)
  = add-two-Even n m p

*N-consecutive-Even : (n : Nat) -> Even (n *N suc n)
*N-consecutive-Even zero = <>
*N-consecutive-Even (suc n)
  rewrite ==-symm (*N-right-suc n (suc n))
  = add-two-Even n (n *N suc n) (*N-consecutive-Even n)

downFrom : Nat -> Nat
downFrom zero = zero
downFrom (suc n) = suc n +N downFrom n

div2 : (n : Nat) -> Even n -> Nat
div2 zero <> = zero
div2 (suc (suc n)) evenn = suc (div2 n evenn)

-- downFrom n == n * (n + 1) / 2
-- 2 * (downFrom n) == n * (n + 1)
downFrom-closed-form : (n : Nat) -> downFrom n +N downFrom n == n *N suc n
downFrom-closed-form zero = refl
downFrom-closed-form (suc n)
  rewrite +N-right-suc (n +N downFrom n) (n +N downFrom n)
  rewrite +N-assoc n (downFrom n) (n +N downFrom n)
  rewrite ==-symm (+N-assoc (downFrom n) n (downFrom n))
  rewrite +N-commut (downFrom n) n
  rewrite +N-assoc n (downFrom n) (downFrom n)
  rewrite downFrom-closed-form n
  rewrite *N-right-suc n (suc n)
  = refl

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

  _ : (3 ,- 5 ,- []) <[ (3 ,- 4 ,- 5 ,- 6 ,- []) ]> (4 ,- 6 ,- [])
  _ = left (right (left (right []split)))

  -- for a predicate to be decidable, it must be decidable for every value
  Dec : {A : Set} -> (A -> Set) -> Set
  Dec {A} P = (x : A) -> (P x -> Zero) + P x

  -- given a decidable predicate and a list, produce two lists
  -- one with all the elements for which the predicate holds
  -- and one with all the elements for which it doesn't
  partition :
    {A : Set} {P : A -> Set} -> Dec P -> (xs : List A) ->
      List A >< \nays ->
      List A >< \yeas ->
        nays <[ xs ]> yeas *
        All (\x -> P x -> Zero) nays *
        All P yeas
  partition p? [] = [] , [] , []split , <> , <>
  partition p? (x ,- xs) with partition p? xs | p? x
  ... | nays , yeas , split , p , q | inl notPx = (x ,- nays) , yeas , left split , (notPx , p) , q
  ... | nays , yeas , split , p , q | inr Px = nays , x ,- yeas , right split , p , (Px , q)

module natsplit where
  -- same idea as with lists
  -- l <[ m ]> r
  data _<[_]>_ : Nat -> Nat -> Nat -> Set where
    zero : zero <[ zero ]> zero

    left : {l r m : Nat} ->
          l <[     m ]>      r ->
      suc l <[ suc m ]>      r

    right : {l r m : Nat} ->
           l <[     m ]>     r ->
           l <[ suc m ]> suc r

  infix 10 _<[_]>_

  _ : 3 <[ 5 ]> 2
  _ = left (left (left (right (right zero))))

  _ : 3 <[ 5 ]> 2
  _ = left (right (left (right (left zero))))

  -- use the splitting to guide you on how to merge the two vectors
  merge :
    {A : Set} {l m r : Nat} ->
    l <[ m ]> r -> Vec A l -> Vec A r ->
    Vec A m
  merge zero xs ys = []
  merge (left spl) (x ,- xs) ys = x ,- merge spl xs ys
  merge (right spl) xs (y ,- ys) = y ,- merge spl xs ys

  _>[_]<_ :
    {A : Set} {l m r : Nat} ->
    Vec A l -> l <[ m ]> r -> Vec A r ->
    Vec A m
  xs >[ spl ]< ys = merge spl xs ys

  -- splitAt 2 [1,2,3,4,5] == ([1,2,3], [4,5])
  -- split (left (right (left (right (left zero))))) [1,2,3,4,5]
  -- [1,3,5] [2,4]
  split : {A : Set} (l m r : Nat) (spl : l <[ m ]> r) (xs : Vec A m) ->
    Vec A l >< \lefts ->
    Vec A r >< \rights ->
      (lefts >[ spl ]< rights) == xs
  split .0 .0 .0 zero [] = [] , [] , refl
  split (suc l) (suc m) r (left spl) (x ,- xs) with split l m r spl xs
  ... | lefts , rights , refl = (x ,- lefts) , rights , refl
  split l (suc m) (suc r) (right spl) (x ,- xs) with split l m r spl xs
  ... | lefts , rights , refl = lefts , (x ,- rights) , refl
