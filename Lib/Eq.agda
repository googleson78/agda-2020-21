module Lib.Eq where

-- traditional equality
-- "the relation that is only reflexive"
-- or the equality/identity path, if you like homotopy type theory
data _==_ {A : Set} : A -> A -> Set where
  refl : (x : A) -> x == x

-- allows us to rewrite
{-# BUILTIN EQUALITY _==_ #-}

infix 10 _==_

-- ap(ply) a function to both sides of an equality
-- alternatively a(ction on)p(aths), again, HoTT
ap : {A B : Set} {x y : A} -> (f : A -> B) -> x == y -> f x == f y
ap f (refl x) = refl (f x)

==-symm : {X : Set} {x y : X} -> x == y -> y == x
==-symm (refl x) = refl x

==-trans : {X : Set} {x y z : X} -> x == y -> y == z -> x == z
==-trans (refl x) (refl .x) = refl x
