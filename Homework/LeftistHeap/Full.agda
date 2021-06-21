{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Full where

open import Lib.Nat
open import Lib.One
open import Lib.Eq
open import Lib.List
open import Lib.Sum
open import Homework.LeftistHeap.Common

data Heap (lower : Priority) : Rank -> Set where

mkNode : {lr rr : Rank} {b : Priority} (p : Priority) -> Leq b p -> Heap p lr -> Heap p rr -> Heap b {!!}
mkNode = {!!}

{-# TERMINATING #-}
merge : {lr rr : Rank} {p : Priority} -> Heap p lr -> Heap p rr -> Heap p {!!}
merge = {!!}

weakenHeap : {r : Rank} (n m : Priority) -> Leq n m -> Heap {!!} r -> Heap {!!} r
weakenHeap = {!!}

singleton : (p x : Priority) -> Leq p x -> Heap {!!} {!!}
singleton = {!!}

insert : {r : Rank} {p : Priority} (x : Priority) -> Heap p r -> Heap {!!} {!!}
insert = {!!}

findMin : {p : Priority} {r : Rank} -> Heap p {!!} -> Priority
findMin = {!!}

delMin : {p : Priority} {r : Rank} -> Heap p {!!} -> Heap p r
delMin = {!!}

minimum : List Priority -> Priority
minimum = {!!}

fromList : (xs : List Priority) -> Heap {!!} {!!}
fromList = {!!}
