{-# OPTIONS --no-unicode #-}


module Lecture.Intro where

-- emacs
-- vscode
-- install party probably


-- <SPC> m l -- презарежда файла

-- class/struct
-- data

-- data Bool = Ff | Tt
-- Set = Type
data Bool : Set where
  ff : Bool
  tt : Bool

-- : ::
-- x :: Bool
-- x = Ff
-- bool x = false;
_ : Bool
_ = ff

-- <SPC> m c - intro variable, case split
-- <SPC> m <SPC> - опитай се да сложиш стойността в дупката
not : Bool -> Bool
not ff = tt
not tt = ff

-- почти всичко е валиден идентификатор в агда
-- (&&) :: Bool -> Bool -> Bool
_&&_ : Bool -> Bool -> Bool
tt && tt = tt
ff && ff = ff
ff && tt = ff
tt && ff = ff

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if ff then t else e = e
if tt then t else e = t

_ : Bool
_ = if tt
    then ff
    else tt


-- struct BoolTwoTuple
-- {
--   bool x;
--   bool y;
-- };

record BoolTwoTuple : Set where
  field
    x' : Bool
    y' : Bool

open BoolTwoTuple public

_ : BoolTwoTuple
_ = record
  {  x' = tt
  ;  y' = tt
  }

-- <SPC> m r - refine
&&-BoolTwoTuple : BoolTwoTuple -> Bool
&&-BoolTwoTuple record { x' = gosho ; y' = pesho } = gosho && pesho



-- import Data.Void
-- data Void
-- webserver :: IO Void
data Zero : Set where

_ : Zero
_ = {!!}

-- Zero съответсвта на лъжа в логиката
zero-elim : {A : Set} -> Zero -> A
zero-elim ()


-- struct {};
-- () :: ()
record One : Set where
  constructor <>

_ : One
_ = <>

-- <SPC> m r -- refine, intro constructor
-- One съответства на тривиална истина
trivial : {A : Set} -> A -> One
trivial _ = <>

-- "булева стойност" vs "свойство"
BoolEq : Bool -> Bool -> Set
BoolEq ff ff = One
BoolEq ff tt = Zero
BoolEq tt ff = Zero
BoolEq tt tt = One

-- x : BoolEq tt tt
-- BoolEq tt tt = One
-- x : One
_ : BoolEq tt tt
_ = <>

-- _ : BoolEq tt ff
-- _ = {!!}

-- <SPC> m ,
bla : Zero -> BoolEq tt ff
bla x = zero-elim x
-- assert (typeof bla === string)

-- _&&_ : Bool -> Bool -> Bool
-- tt && tt = tt
-- ff && ff = ff
-- ff && tt = ff
-- tt && ff = ff

-- BoolEq (x && y) (y && x) == One
-- x ~ ff
-- y ~ ff
-- BoolEq (ff && ff) (ff && ff)
-- BoolEq ff ff
-- One : Set

-- BoolEq (x && y) (y && x) ~ One
&&-commut : (x y : Bool) -> BoolEq (x && y) (y && x)
&&-commut ff ff = <>
&&-commut ff tt = <>
&&-commut tt ff = <>
&&-commut tt tt = <>
-- !=< "различен тип от"















