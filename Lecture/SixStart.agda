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
