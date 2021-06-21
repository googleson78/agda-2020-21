{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ordered where

open import Lib.Sum
open import Lib.One
open import Homework.LeftistHeap.Common
open import Lib.Nat

-- parametrised by the lower bound of the heap
data Heap (lower : Priority) : Set where


rank : {lower : Priority} -> Heap lower -> Rank
rank = {!!}

mkNode :
  {lower : Priority} (x : Priority) ->
  Leq lower x -> Heap x -> Heap x -> Heap lower
mkNode = {!!}

{-# TERMINATING #-}
merge :
  {lower : Priority} ->
  Heap lower -> Heap lower -> Heap lower
merge = {!!}

singleton : {lower : Priority} (x : Priority) -> Leq lower x -> Heap lower
singleton = {!!}

weakenHeap : (n m : Priority) -> Leq n m -> Heap {!!} -> Heap {!!}
weakenHeap = {!!}

insert : {lower : Priority} (x : Priority) -> Heap lower -> Heap {!!}
insert = {!!}

findMin : {lower : Priority} -> Heap lower -> Maybe Priority
findMin = {!!}

delMin : {lower : Priority} -> Heap lower -> Maybe (Heap lower)
delMin = {!!}
