{-# OPTIONS --no-unicode #-}
module Lecture.SixStart where

open import Lib.Nat
open import Lib.Eq
open import Lib.Sum
open import Lib.Zero
open import Lib.One

data Type : Set where
  base : Nat -> Type
  _=>_ : Type -> Type -> Type

infixr 11 _=>_

alpha : Type
alpha = base 0

beta : Type
beta = base 1

gamma : Type
gamma = base 2

_ : Type
_ = (alpha => alpha) => beta

_ : Type
_ = alpha => alpha => beta

_ : alpha => alpha => beta == alpha => (alpha => beta)
_ = refl


-- Context : Set
-- Context = List Type
-- alpha ,- beta ,- gamma

data Context : Set where
  [] : Context
  _-,_ : Context -> Type -> Context

infixl 11 _-,_

_ : Context
_ = [] -, alpha

_ : Context
_ = [] -, alpha -, beta

_ : [] -, alpha -, beta == ([] -, alpha) -, beta
_ = refl

delta : Context
delta = [] -, alpha -, beta

{-
data Lam (n : Nat) : Set where
  var : Fin n -> Lam n
  app : Lam n -> Lam n -> Lam n
  lam : Lam (suc n) -> Lam n
-}

{-
data _In_ (x : A) : List A -> Set where
    here : {xs : List A} -> x In (x ,- xs)
    there : {y : A} {xs : List A} -> x In xs -> x In (y ,- xs)
-}

data _In_ : Type -> Context -> Set where
  Z : {tau : Type} {gamma : Context} -> tau In (gamma -, tau)
  S : {sigma tau : Type} {gamma : Context} -> tau In gamma -> tau In (gamma -, sigma)

_ : beta In delta
_ = Z

_ : alpha In delta
_ = S Z

data Lam (gamma : Context) : Type -> Set where
  var : {tau : Type} -> tau In gamma -> Lam gamma tau
  app : {sigma1 sigma2 : Type} -> Lam gamma (sigma1 => sigma2) -> Lam gamma sigma1 -> Lam gamma sigma2
  lam : {sigma1 sigma2 : Type} -> Lam (gamma -, sigma1) sigma2 -> Lam gamma (sigma1 => sigma2)

_ : Lam ([] -, alpha) alpha
_ = var Z

_ : Lam ([] -, beta -, alpha) beta
_ = var (S Z)

-- identity : alpha => alpha
_ : Lam [] (alpha => alpha)
_ = lam (var Z)

-- k : alpha => beta => alpha = (lam_x (lam_y x))
-- Lam ([] -, alpha) (beta => alpha)
_ : Lam [] (alpha => beta => alpha)
_ = lam (lam (var (S Z)))


-- TODO: explain at lecture
-- mechanism so we can use the usual debruijn indices instead of Ins
length : Context -> Nat
length [] = 0
length (ts -, _) = suc (length ts)

ix : (n : Nat) (ctxt : Context) -> (Lt n (length ctxt)) -> Type
ix zero (ts -, x) p = x
ix (suc n) (ts -, x) p = ix n ts p

ixIn : (n : Nat) (ctxt : Context) (p : Lt n (length ctxt)) -> ix n ctxt p In ctxt
ixIn zero (ctxt -, x) p = Z
ixIn (suc n) (ctxt -, x) p = S (ixIn n ctxt p)

`_ : {ctxt : Context} (n : Nat) -> {p : Lt n (length ctxt)} -> Lam ctxt (ix n ctxt p)
` n = var (ixIn n _ _)

-- same examples as above, but with `_
_ : Lam ([] -, alpha) alpha
_ = ` 0

_ : Lam ([] -, beta -, alpha) beta
_ = ` 1

-- identity : alpha => alpha
_ : Lam [] (alpha => alpha)
_ = lam (` 0)

-- k : alpha => beta => alpha = (lam_x (lam_y x))
-- Lam ([] -, alpha) (beta => alpha)
_ : Lam [] (alpha => beta => alpha)
_ = lam (lam (` 1))

{-
-- a renaming is a way for us to send any type in one context to another
Renaming : Context -> Context -> Set
Renaming gamma delta = {tau : Type} -> tau In gamma -> tau In delta

-- the identity renaming, does nothing
idRename : {gamma : Context} -> Renaming gamma gamma
idRename = {!!}

-- a renaming that shifts all the variables up by one
-- useful when we encounter a lambda, which introduces a free variable
-- to the head of our context
shift1Rename : {gamma : Context} {sigma : Type} -> Renaming gamma (gamma -, sigma)
shift1Rename = ?

-- we can extend Renamings
ext :
  {gamma delta : Context} {sigma : Type} ->
  Renaming gamma delta ->
  Renaming (gamma -, sigma) (delta -, sigma)
ext = {!!}

-- applying a renaming to a term
-- in particular, we can create a new variable, like in shiftUp1
-- by renaming with S : tau In gamma -> tau In (gamma -, sigma)
rename :
  {gamma delta : Context} ->
  -- if we know how to go from gamma to delta for any types in gamma
  Renaming gamma delta ->
  -- then we can also do the transition for terms
  {tau : Type} -> Lam gamma tau -> Lam delta tau
rename = {!!}

-- again, as with untyped Lams, we need to explicitly specify what our context is
-- because a single term is valid in many contexts
withContext : {tau : Type} (gamma : Context) -> Lam gamma tau -> Lam gamma tau
withContext _ x = x

-- convenience synonyms for small contexts
pattern [_] x = [] -, x
pattern [_,_] x y = [] -, x -, y
pattern [_,_,_] x y z = [] -, x -, y -, z

-- for example
_ : Context
_ = [ base 1 ]

_ : Context
_ = [ base 2 , (base 1 => base 2) , base 1 ]

-- our id renaming should do nothing
_ : withContext [ base 5 ] (rename idRename (` 0)) == ` 0
_ = refl

_ : withContext [] (rename idRename (lam {_} {base 3} (` 0))) == lam (` 0)
_ = refl

-- and our shift renaming should.. shift
_ :
  withContext [ base 42 , base 69 ]
    (rename shift1Rename
      (withContext [ base 42 ] (` 0)))
  ==
  ` 1
_ = refl

-- but it should take care not to touch bound variables
_ :
  withContext [ base 42 , base 69 ]
    (rename shift1Rename
      (withContext [ base 42 ]
        (app
          (lam {_} {base 42} (` 0))
          (` 0))))
  ==
  app (lam (` 0)) (` 1)
_ = refl

-- a substitution is a way to map all the variables in one context to terms in another context
Substitution : Context -> Context -> Set
Substitution gamma delta = {tau : Type} -> tau In gamma -> Lam delta tau

-- the substitution that replaces all variables with themselves
idSubst : {gamma : Context} -> Substitution gamma gamma
idSubst = {!!}

-- we can extend substitutions
-- we'll need to rename here, in order to "shift" all our variables
extSubstitution :
  {gamma delta : Context} {sigma : Type} ->
  Substitution gamma delta ->
  Substitution (gamma -, sigma) (delta -, sigma)
extSubstitution = {!!}

-- and finally, we can apply substitutions to terms
substitute :
  {gamma delta : Context} {tau : Type} ->
  Substitution gamma delta ->
  Lam gamma tau -> Lam delta tau
substitute = {!!}

-- a substitution that essentially performs one computation
-- the idea here is that we have a situation like so
-- app (lam N) M
-- and we want to "apply" the lambda to the argument M
-- "coincidentally", the lambda has just introduced a variable for us to use
-- with the M we have, and the types line up, because of how the app constructor looks
-- we need to substitute M for our free variable, but also not forget to *shift down*
-- all our other variables, as they have just had one lambda removed
reduceSubst : {gamma : Context} {tau : Type} -> Lam gamma tau -> Substitution (gamma -, tau) gamma
reduceSubst = {!!}

-- what we actually (might eventually) need is a single variable substitution
-- this is due to the fact that when we want to calculate an expression, like
-- (λx. λy. x y) z
-- or in other words (e.g.)
-- (λλ 1 0) 2
-- we only need to substitute the outermost lambda, which is always at the head of our context
-- due to how the lam constructor for Lams is made
--
-- use substitute, and construct a suitable substitution
substitute1 :
  {gamma : Context} {tau sigma : Type} ->
  Lam (gamma -, sigma) tau ->
  Lam gamma sigma ->
  Lam gamma tau
substitute1 N M = {!!}

_ :
  withContext [ base 69 , base 42 ]
    (substitute1 (` 0) (` 1))
  ==
  (` 1)
_ = refl

_ :
  withContext [ base 1337 , base 42 ]
    (substitute1 (lam {_} {base 69} (` 0)) (` 1))
  ==
  lam (` 0)
_ = refl

foo0 : Lam [ base 0 => base 0 ] (base 0 => base 0)
foo0 = lam (app (` 1) (app (` 1) (` 0)))

foo1 : Lam [] (base 0 => base 0)
foo1 = lam (` 0)

foo2 : Lam [] (base 0 => base 0)
foo2 = lam (app (lam (` 0)) (app (lam (` 0)) (` 0)))

_ : substitute1 foo0 foo1 == foo2
_ = refl

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

data Fin<= : {n : Nat} -> Fin n -> Fin n -> Set where
  ozero : {n : Nat} {x : Fin (suc n)} -> Fin<= zero x
  osuc : {n : Nat} {x y : Fin n} -> Fin<= x y -> Fin<= (suc x) (suc y)

decFin<= : {n : Nat} (x y : Fin n) -> Dec (Fin<= x y)
decFin<= zero y = yes ozero
decFin<= (suc x) zero = no \ ()
decFin<= (suc x) (suc y) with decFin<= x y
... | no !x<=y = no \{ (osuc x1) -> !x<=y x1}
... | yes x<=y = yes (osuc x<=y)

ixOf : {ctxt : Context} {tau : Type} -> tau In ctxt -> Fin (suc (length ctxt))
ixOf = {!!}

insert : (tau : Type) (gamma : Context) -> Fin (suc (length gamma)) -> Context
insert = {!!}

-- when we insert after our variable, it doesn't need to change
insertInNoShift :
  {tau rho : Type} {gamma : Context}
  (c : (Fin (suc (length gamma))))
  (k : tau In gamma) ->
  (Fin<= c (ixOf k) -> Zero) ->
  tau In insert rho gamma c
insertInNoShift = {!!}

-- when we insert before our variable, we need to shift it once
insertInShift :
  {tau rho : Type} {gamma : Context}
  (c : (Fin (suc (length gamma))))
  (k : tau In gamma) ->
  Fin<= c (ixOf k) ->
  tau In insert rho gamma c
insertInShift = {!!}

shift : {tau : Type} {gamma : Context} (rho : Type) (c : Fin (suc (length gamma))) -> Lam gamma tau -> Lam (insert rho gamma c) tau
shift = {!!}

shift0 : {tau : Type} {gamma : Context} (rho : Type) -> Lam gamma tau -> Lam (gamma -, rho) tau
shift0 = {!!}

data Fin< : {n : Nat} -> Fin n -> Fin n -> Set where
  ozero : {n : Nat} {x : Fin n} -> Fin< zero (suc x)
  osuc : {n : Nat} {x y : Fin n} -> Fin< x y -> Fin< (suc x) (suc y)

compareFin : {n : Nat} (x y : Fin n) -> Fin< x y + Fin< y x + x == y
compareFin zero zero = inr (inr refl)
compareFin zero (suc y) = inl ozero
compareFin (suc x) zero = inr (inl ozero)
compareFin (suc x) (suc y) with compareFin x y
... | inl x1 = inl (osuc x1)
... | inr (inl x1) = inr (inl (osuc x1))
... | inr (inr refl) = inr (inr refl)

weakenFin : {m n : Nat} -> Fin n -> n <= m -> Fin m
weakenFin zero (osuc n<=m) = zero
weakenFin (suc x) (osuc n<=m) = suc (weakenFin x n<=m)

lengthen :
  (rho : Type) (gamma : Context) (c : Fin (suc (length gamma))) ->
  length gamma <= length (insert rho gamma c)
lengthen = {!!}

subst :
  {tau : Type} (gamma : Context) (rho : Type) (k : Fin (suc (length gamma))) ->
  Lam (insert rho gamma k) tau ->
  Lam gamma rho ->
  Lam gamma tau
subst gamma rho k (app M1 M2) N = {!!}
subst gamma rho k (lam {sg1} M) N = {!!}
-- struggle
subst gamma rho k (var i) N = {!!}
-}
