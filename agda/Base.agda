module Base where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

data _==_ {l : Level}{A : Set l}(a : A) : A -> Set l where
  refl : a == a
infix 0 _==_

{-# BUILTIN EQUALITY _==_ #-}

cong : forall {a b} {A : Set a} {B : Set b} {x y : A} (f : A -> B) -> x == y -> f x == f y
cong f refl = refl

cong2 : forall {a b c} {A : Set a} {B : Set b} {C : Set c}
        {a a' b b'} (f : A -> B -> C) -> a == a' -> b == b' -> f a b == f a' b'
cong2 f refl refl = refl

sym : forall {a} {A : Set a} {x y : A} -> x == y -> y == x
sym refl = refl

trans : forall {a} {A : Set a} {x y z : A} -> x == y -> y == z -> x == z
trans refl q = q

subst : forall {a p} {A : Set a} (P : A -> Set p) {x y : A} -> x == y -> P x -> P y
subst P refl px = px

IsProp : forall {a} -> Set a -> Set a
IsProp A = (x y : A) -> x == y

==IsProp : forall {a A x y} -> IsProp (_==_ {a} {A} x y)
==IsProp refl refl = refl

record Sg {a b} (A : Set a) (B : A -> Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Sg public
infixr 1 _,_

_*_ : forall {a b} -> Set a -> Set b -> Set (a ⊔ b)
A * B = Sg A \ _ -> B
infixr 4 _*_

mapSg : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : A -> Set b} {B' : A' -> Set b'}
        (fa : A -> A') -> (forall {a} -> B a -> B' (fa a)) -> Sg A B -> Sg A' B'
mapSg fa fb (a , b) = fa a , fb b

uncurry : forall {a b c} {A : Set a} {B : A -> Set b} {C : (a : A) -> B a -> Set c} ->
          ((a : A) (b : B a) -> C a b) -> (ab : Sg A B) -> C (fst ab) (snd ab)
uncurry f (a , b) = f a b

map* : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} ->
       (A -> A') -> (B -> B') -> A * B -> A' * B'
map* fa fb = mapSg fa fb
