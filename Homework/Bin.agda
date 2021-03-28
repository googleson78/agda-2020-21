{-# OPTIONS --no-unicode #-}

module Homework.Bin where

import Lib.Nat as Nat
open Nat using (Nat; _+N_)
open import Lib.Eq
open import Lib.Sigma
open import Lib.Zero
open import Lib.One

data Bin : Set where
  end : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

infixr 12 _O
infixr 12 _I

_ : Bin
_ = end I O I

suc : Bin -> Bin
suc = {!!}

_ : suc end == end I
_ = refl

_ : suc (end I I) == end I O O
_ = refl

toNat : Bin -> Nat
toNat = {!!}

_ : toNat (end I I I) == 7
_ = refl

_ : toNat (end I I O) == 6
_ = refl

_ : toNat (end O) == 0
_ = refl

_ : toNat end == 0
_ = refl

fromNat : Nat -> Bin
fromNat = {!!}

_ : fromNat 0 == end
_ = refl

_ : fromNat 1 == end I
_ = refl

_ : fromNat 8 == end I O O O
_ = refl

toNat-suc : (b : Bin) -> toNat (suc b) == Nat.suc (toNat b)
toNat-suc = {!!}

to-from-id : (n : Nat) -> toNat (fromNat n) == n
to-from-id = {!!}

data LeadingOne : Bin -> Set where
  endI : LeadingOne (end I)
  _O : {b : Bin} -> LeadingOne b -> LeadingOne (b O)
  _I : {b : Bin} -> LeadingOne b -> LeadingOne (b I)

data Can : Bin -> Set where
  end : Can end
  leadingOne : {b : Bin} -> LeadingOne b -> Can b

suc-LeadingOne : (b : Bin) -> LeadingOne b -> LeadingOne (suc b)
suc-LeadingOne = {!!}

suc-Can : (b : Bin) -> Can b -> Can (suc b)
suc-Can = {!!}

fromNat-Can : (n : Nat) -> Can (fromNat n)
fromNat-Can = {!!}

_+B_ : Bin -> Bin -> Bin
_+B_ = {!!}

infixr 11 _+B_

_ : end +B end I I I I == end I I I I
_ = refl

_ : end I O O +B end == end I O O
_ = refl

_ : end I I +B end I I I I == end I O O I O
_ = refl

_ : end I I I +B end I O I == end I I O O
_ = refl

+B-right-end : (b : Bin) -> b +B end == b
+B-right-end = {!!}

+B-left-suc : (b v : Bin) -> suc b +B v == suc (b +B v)
+B-left-suc = {!!}

+B-right-suc : (b v : Bin) -> b +B suc v == suc (b +B v)
+B-right-suc = {!!}

fromNat-+N-+B-commutes : (n m : Nat) -> fromNat (n +N m) == fromNat n +B fromNat m
fromNat-+N-+B-commutes = {!!}

+B-same-shift : (b : Bin) -> LeadingOne b -> b +B b == b O
+B-same-shift = {!!}

from-to-id-Can : (b : Bin) -> Can b -> fromNat (toNat b) == b
from-to-id-Can = {!!}
