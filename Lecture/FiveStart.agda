{-# OPTIONS --no-unicode #-}
module Lecture.FiveStart where

open import Lib.Nat
open import Lib.Eq
open import Lib.Sum
open import Lib.Zero
open import Lib.One
open import Lib.List
open import Lib.Sigma

-- mention =[] being useful for writing down examples later!

-- Fin n has n inhabitants
-- (x : Fin n) -> x < n
-- x ∈ [0..n)
data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

-- [0..1) -> [0, 1) -> {0}
_ : Fin 1
_ = zero

-- [0..2) -> [0,1,2) -> {0, 1}
_ : Fin 2
_ = zero

_ : Fin 5
_ = suc (suc (suc (suc zero)))

-- Leq : Nat -> Nat -> Set
-- Leq zero m = One
-- Leq (suc n) zero = Zero
-- Leq (suc n) (suc m) = Leq n m
--
-- Leq 3 5
-- Leq 2 4
-- Leq 1 3
-- Leq 0 2
-- One
-- _ : Nat >< \m -> Leq m 5
-- _ = 3 , _
--
-- f : (n : Nat) -> {Leq n 5} -> Nat >< \m -> Leq m 5
-- f n {x} = n , x
--
-- _ : f 3 == f 3
-- _ = refl

-- [0..) -> [0) -> {}
-- _ : Fin 0
-- _ = {!zero!}

{-
toNat : {n : Nat} -> Fin n -> Nat
toNat = {!!}

-- express < using <=
-- (without! using ==)
_<_ : Nat -> Nat -> Set
n < m = {!!}

_ : 3 < 5
_ = {!!}

3NotLessThan2 : 3 < 2 -> Zero
3NotLessThan2 = {!!}

<-suc : (n : Nat) -> n < suc n
<-suc = {!!}

-- convert from a Nat to a Fin
-- note that we can't just write (n : Nat) -> Fin n
-- because e.g. it's not true that 3 can be expressed as (suc (suc (suc zero))) : Fin 3
--
-- we allow for an arbitrary m, instead of just Fin (suc n), because it's more convenient
-- (e.g. for fromNat-toNat-id)
fromNat : {m : Nat} -> (n : Nat) -> n < m -> Fin m
fromNat = {!!}

-- write down the calculated version of <
-- this is useful because later we will want to write literals (like 1)
-- and have them mean Fins with as little boilerplate as possible
-- which includes not having to write down the explicit proof for < (which fromNat) requires
-- instead, if we provide a calculated version, when we give come constant (like 1)
-- agda will be able to automatically figure out the required proof, by using this definition
Lt : Nat -> Nat -> Set
Lt = {!!}

-- prove that the calculated version implies the regular one,
-- so that we may provide the regular proof to fromNat later
Lt-< : (n m : Nat) -> Lt n m -> n < m
Lt-< = {!!}

-- the "smart constructor" for Fins mentioned in the comment on Lt
-- it allows us to write "Fin literals" with almost no hassle
-- you'll need to expose *all* the implicit arguments here
-- see the examples below
fin : {m : Nat} -> (n : Nat) -> {Lt n m} -> Fin m
fin = {!!}
-- there is actually an even better way to do this - https://agda.readthedocs.io/en/v2.6.1.3/language/literal-overloading.html
-- but it requires us to use some machinery we haven't introduced yet

_ : Fin 3
_ = fin 2
-- vs
_ : Fin 3
_ = fromNat 2 (osuc (osuc (osuc ozero)))
-- vs
_ : Fin 3
_ = suc (suc (zero))

-- doesn't work, as expected, because 2 is not a Fin 2
-- _ : Fin 2
-- _ = fin 2

_ : Fin 5
_ = fin 2

_ : Fin 5
_ = fin 3

toNat-fromNat-id : (n : Nat) -> n == toNat (fromNat n (<-suc n))
toNat-fromNat-id = {!!}

toNat-< : {n : Nat} -> (x : Fin n) -> toNat x < n
toNat-< = {!!}

-- weaken, because we allow *more* values in the new Fin,
-- meaning we have *less* information about what the result actually is
weakenFin : {m n : Nat} -> Fin n -> n <= m -> Fin m
weakenFin = {!!}

-- specialised, useful later
-- look at <=-suc in Lib.Nat
weakenFinSuc : {n : Nat} -> Fin n -> Fin (suc n)
weakenFinSuc = {!!}

<-<= : {n m : Nat} -> n < m -> n <= m
<-<= = {!!}

fromNat-toNat-id : {m n : Nat} (x : Fin n) (p : n <= m) -> x == fromNat (toNat x) (toNat-< x)
fromNat-toNat-id = {!!}

decEqFin : {n : Nat} -> (x y : Fin n) -> Dec (x == y)
decEqFin = {!!}

-- name the constructors var, app, lam
-- for everything below to work ^^
data Lam (n : Nat) : Set where

-- construct a variable from a Nat directly
-- you'll need to expose the Lt arg
-- this is a convenient prefix synonym for vars, allows us to write things like
-- ` 4
-- instead of
-- var (fin 2) or var (suc (suc zero))
-- most of the time
`_ : {m : Nat} -> (n : Nat) -> {Lt n m} -> Lam m
`_ n {x} = ?

-- λx. λy. x (x z)
-- \x -> \y -> x (x z)
_ : Lam 1
_ = lam (lam (app (` 0) (app (` 0) (` 1))))

-- define the id function using nameless terms
lamId : Lam 0
lamId = {!!}

-- define the const function using nameless terms
-- taking two arguments, and always returning the first one
lamK : Lam 0
lamK = {!!}

-- implement the following function
s : {A B C : Set} -> (A -> B -> C) -> (A -> B) -> A -> C
s = {!!}

-- translate s into Lam
lamS : Lam 0
lamS = {!!}

-- a purely syntactic trick, to allow us to specify beforehand
-- how many free variables our lambda term will have when it is ambiguous
-- for example lam (var zero)
-- could have as many free variables as we like
-- agdas type system doesn't like this, as it cannot infer implicits well because of it
-- we can either do something like
-- lam {3} (var zero)
-- to explicitly say how many there can be
-- or we can use this trick, writing instead
-- withFree 3 (lam (var zero))
-- to mean the same thing
withFree : (n : Nat) -> Lam n -> Lam n
withFree _ x = x

_ :
  withFree 3 (lam (var zero))
  ==
  lam (var zero)
_ = refl
-- vs
_ :
  lam {3} (var zero)
  ==
  lam (var zero)
_ = refl

_ :
  lam {3} (var zero)
  ==
  withFree 3 (lam (var zero))
_ = refl

-- uncomment this temporarily, and note how without the annotations, agda gets confused:
-- _ :
--   lam (var zero)
--   ==
--   lam (var zero)
-- _ = refl

dec<= : (n m : Nat) -> Dec (n <= m)
dec<= = {!!}

dec< : (n m : Nat) -> Dec (n < m)
dec< = {!!}

-- "shift"/increment all the free variables in the given lambda term up by one
shiftUp1 : {n : Nat} -> Nat -> Lam n -> Lam (suc n)
shiftUp1 c t = {!!}

shiftUp10 : {n : Nat} -> Lam n -> Lam (suc n)
shiftUp10 = shiftUp1 0

-- what does shifting
-- λ 0
-- result in?
-- note how we have to give an explicit argument for at least the lambda in the beginning
-- for type inference for implicits to be able to work
-- (alternatively we could've given one for the var in the end)
-- this comes down to the fact that e the lambda term we've given is not restricted
-- to being in any given Lam n - n could be anything, as long as it has *enough* free vars
_ :
  withFree 1 (shiftUp10 (lam (` 0)))
  ==
  {!!}
_ = refl
-- what does shifting
-- λ λ 1
-- result in?
_ :
  shiftUp10 (withFree 2 (lam (lam (` 1))))
  ==
  {!!}
_ = refl

-- what does shifting
-- λ λ 3
-- result in?
_ :
  shiftUp10 (withFree 4 (lam (lam (` 3))))
  ==
  {!!}
_ = refl

-- what does shifting
-- λ λ (0 (0 2)
-- result in?
_ :
  shiftUp10 (withFree 4 (lam (lam (app (` 1) (app (` 0) (` 2))))))
  ==
  {!!}
_ = refl

_[_=>_] : {n : Nat} -> Lam n -> Fin n -> Lam n -> Lam n
_[_=>_] = {!!}

-- what does substituting 2 for 3 in 1 result in?
--
-- note that we have to give our lambda term enough free vars
-- for the substitution to be applicable, even if we're not using them!
_ :
  withFree 4 ((` 1) [ fin 2 => `_ 3 ])
  ==
  {!!}
_ = refl

-- what does substituting 2 for 3 in 2 result in?
-- note how we still have to account for the free vars!
_ :
  withFree 4 ((` 2) [ fin 2 => `_ 3 ])
  ==
  {!!}
_ = refl

-- what does substituting 2 for 3 in λ0 result in?
_ :
  withFree 4 (lam (` 0) [ fin 2 => `_ 3 ])
  ==
  {!!}
_ = refl

-- what does substituting 3 for 5 in λ3 result in?
_ :
  withFree 6 (lam (` 3)) [ fin 2 => ` 5 ]
  ==
  {!!}
_ = refl

-- what does substituting 0 for 01 in λ0 result in?
_ :
  withFree 4 (lam (` 0)) [ fin 0 => app (` 0) (` 1) ]
  ==
  {!!}
_ = refl

-- what does substituting 0 for λ01 in 0(λ01) result in?
_ :
  withFree 2 (app (` 0) (lam (app (` 0) (` 1)))) [ fin 0 => lam (app (` 0) (` 1)) ]
  ==
  {!!}
_ = refl

-- we could use strings here, but instead we'll use Nats
-- meaning 1 will "stand for" x₁, 8 for x₈, etc
data NamedLam : Set where
  var : Nat -> NamedLam
  app : NamedLam -> NamedLam -> NamedLam
  lam_>_ : Nat -> NamedLam -> NamedLam

-- give names to the lambda function, using the provided context
name : (ctxt : List Nat) -> Lam (length ctxt) -> NamedLam
name ctxt t = {!!}
-}
