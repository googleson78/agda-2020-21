{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ranked where

open import Homework.LeftistHeap.Common
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Nat
open import Lib.Eq

-- type index, since we will need it to vary for the different constructors
data Heap : Rank -> Set where

mkNode :
  {lr rr : Rank} ->
  Priority -> Heap lr -> Heap rr -> Heap {!!}
mkNode = {!!}

{-# TERMINATING #-}
merge :
  {lr rr : Rank} ->
  Heap lr -> Heap rr -> Heap {!!}
merge = {!!}

singleton : Priority -> Heap {!!}
singleton = {!!}

insert : {r : Rank} -> Priority -> Heap r -> Heap {!!}
insert = {!!}

findMin : {r : Rank} -> Heap {!!} -> Priority
findMin = {!!}

delMin : {r : Rank} -> Heap {!!} -> Heap r
delMin = {!!}
