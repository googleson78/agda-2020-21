{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Untyped where

open import Homework.LeftistHeap.Common
open import Lib.Sum
open import Lib.Nat

data Heap : Set where
  empty : Heap
  node : Rank -> Priority -> Heap -> Heap -> Heap

-- nothing is preventing us from making heaps that break the invariant
-- or from not preserving it in our functions

-- note how 2 is not < 0
wrongOrder : Heap
wrongOrder = node 2 2 (node 1 0 empty empty) empty

-- note how the left empty has a lower rank than the right node
wrongRankprop : Heap
wrongRankprop = node 2 0 empty (node 1 5 empty empty)

-- note how the rank assigned here is just wrong
wrongRank : Heap
wrongRank = node 1337 0 empty empty

-- for the ordering
-- 1 <= 2
-- 1 <= 3
-- also, the ranks are correct, since 3 = 1 + (1 + 1)
-- and the rank property is preserved, since
-- 1 (rank of the right tree) <= 1 (rank of the left tree)
proper : Heap
proper = node 3 1 (node 1 2 empty empty) (node 1 3 empty empty)

rank : Heap -> Rank
rank empty = 0
rank (node r _ _ _) = r

mkNode : Priority -> Heap -> Heap -> Heap
mkNode x h1 h2 with decLeq (rank h1) (rank h2)
... | inl rankh1<=rankh2
  = node (suc (rank h2 +N rank h1)) x h2 h1
... | inr rankh2<=rankh1
  = node (suc (rank h1 +N rank h2)) x h1 h2

{-# TERMINATING #-}
merge : Heap -> Heap -> Heap
merge empty h2 = h2
merge h1 empty = h1
merge h1@(node rank1 x1 l1 r1) h2@(node rank2 x2 l2 r2) with decLeq x1 x2
... | inl x1<=x2
  = mkNode x1 l1 (merge r1 h2)
... | inr x2<=x1
  = mkNode x2 l2 (merge r2 h1)

singleton : Priority -> Heap
singleton x = node 1 x empty empty

insert : Priority -> Heap -> Heap
insert x h = merge (singleton x) h

findMin : Heap -> Maybe Priority
findMin empty = no
findMin (node _ x _ _) = yes x

delMin : Heap -> Maybe Heap
delMin empty = no
delMin (node rank x l r) = yes (merge l r)
