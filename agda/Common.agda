module Common where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

id : forall {l} {A : Set l} -> A -> A
id x = x

infixr 5 _o_
_o_ : forall {a b c} {A : Set a} {B : A -> Set b} {C : forall {a} -> B a -> Set c}
      (f : forall {a} (b : B a) -> C b) (g : forall a -> B a) a -> C (g a)
(f o g) x = f (g x)

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

data Zero : Set where

Zero-elim : forall {l} {A : Set l} -> Zero -> A
Zero-elim ()

Not : forall {a} -> Set a -> Set a
Not A = A -> Zero

record One : Set where
  constructor <>
open One public

data Two : Set where
  tt ff : Two

not : Two -> Two
not tt = ff
not ff = tt

and : Two -> Two -> Two
and tt y = y
and ff y = ff

or : Two -> Two -> Two
or tt y = tt
or ff y = y

xor : Two -> Two -> Two
xor tt tt = ff
xor tt ff = tt
xor ff tt = tt
xor ff ff = ff

_=>_ : Two -> Two -> Two
tt => y = y
ff => y = tt

T : Two -> Set
T tt = One
T ff = Zero

->-or : forall {x y} -> T x -> T (or x y)
->-or {tt} a = <>
->-or {ff} ()

xor-transfer : forall {x x' y} -> xor x y == xor x' y -> x == x'
xor-transfer {tt} {tt} {y} eq = refl
xor-transfer {tt} {ff} {tt} ()
xor-transfer {tt} {ff} {ff} ()
xor-transfer {ff} {tt} {tt} ()
xor-transfer {ff} {tt} {ff} ()
xor-transfer {ff} {ff} {y} eq = refl

or-xor : forall {x y} -> and x y == ff -> xor (or x y) x == y
or-xor {tt} {y} eq = sym eq
or-xor {ff} {tt} eq = refl
or-xor {ff} {ff} eq = refl

and-xor : forall {x y} -> (T x -> T y) -> and x (xor y x) == ff
and-xor {tt} {tt} impl = refl
and-xor {tt} {ff} impl = Zero-elim (impl <>)
and-xor {ff} {y} impl = refl

data Dec {x} (X : Set x) : Set x where
  yes : (p : X) -> Dec X
  no : (np : X -> Zero) -> Dec X

mapDec : forall {x y X Y} -> (X -> Y) -> (Y -> X) -> Dec {x} X -> Dec {y} Y
mapDec f g (yes p) = yes (f p)
mapDec f g (no np) = no (λ z → np (g z))

floor : forall {x X} -> Dec {x} X -> Two
floor (yes p) = tt
floor (no np) = ff

Auto : forall {x X} -> Dec {x} X -> Set
Auto = T o floor

fromWitness : forall {x X} {X? : Dec {x} X} -> X -> Auto X?
fromWitness {X? = yes p} x = <>
fromWitness {X? = no np} x = Zero-elim (np x)

toWitness : forall {x X} {X? : Dec {x} X} -> Auto X? -> X
toWitness {X? = yes x} auto = x
toWitness {X? = no nx} ()

DecEq : forall {x} -> Set x -> Set x
DecEq X = (x y : X) -> Dec (x == y)

_==Two?_ : DecEq Two
tt ==Two? tt = yes refl
tt ==Two? ff = no (λ ())
ff ==Two? tt = no (λ ())
ff ==Two? ff = yes refl

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+N_ : Nat -> Nat -> Nat
zero   +N n = n
succ m +N n = succ (m +N n)

data CompareNat : Nat -> Nat -> Set where
  lt  : (m k : Nat) -> CompareNat m (succ (m +N k))
  gte : (k n : Nat) -> CompareNat (n +N k) n

compareNat : (m n : Nat) -> CompareNat m n
compareNat zero     zero     = gte zero zero
compareNat zero     (succ n) = lt zero n
compareNat (succ m) zero     = gte (succ m) zero
compareNat (succ m) (succ n) with compareNat m n
compareNat (succ m) (succ .(succ (m +N k))) | lt .m k = lt _ _
compareNat (succ .(n +N k)) (succ n)        | gte k .n = gte _ _

succInj : forall {m n} -> succ m == succ n -> m == n
succInj refl = refl

_==Nat?_ : DecEq Nat
zero ==Nat? zero = yes refl
zero ==Nat? succ n = no (λ ())
succ m ==Nat? zero = no (λ ())
succ m ==Nat? succ n = mapDec (cong succ) succInj (m ==Nat? n)

data List {a} (A : Set a) : Set a where
  nil  : List A
  _::_ : A -> List A -> List A

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

map* : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} ->
       (A -> A') -> (B -> B') -> A * B -> A' * B'
map* fa fb = mapSg fa fb

_*?_ : forall {a b A B} -> Dec {a} A -> Dec {b} B -> Dec (A * B)
_*?_ (yes a) (yes b) = yes (a , b)
_*?_ (yes a) (no nb) = no (\ { (_ , b) -> nb b })
_*?_ (no na) B? = no (\ { (a , b) -> na a })

infixr 5 _::_

::Inj : forall {a} {A : Set a} {x0 x1 : A} {l0 l1} ->
        x0 :: l0 == x1 :: l1 -> (x0 == x1) * (l0 == l1)
::Inj refl = refl , refl

--------------------------------------------------------------------------------
data LTy : Set where
  KEY           : LTy
  LIST          : LTy -> LTy
  _-o_ _<**>_ _&_  : LTy -> LTy -> LTy

infixr 5 _-o_

--------------------------------------------------------------------------------
-- Permutations and so on
_++_ : forall {x} {X : Set x} -> List X -> List X -> List X
nil       ++ l2 = l2
(x :: l1) ++ l2 = x :: (l1 ++ l2)

fold : forall {x y} {X : Set x} {Y : Set y} -> Y -> (X -> Y -> Y) -> List X -> Y
fold n c nil = n
fold n c (x :: l) = c x (fold n c l)

++nil : forall {x} {X : Set x} -> (l : List X) -> l ++ nil == l
++nil nil      = refl
++nil (x :: l) rewrite ++nil l = refl

++Assoc : forall {x} {X : Set x} (l1 l2 l3 : List X) -> ((l1 ++ l2) ++ l3) == (l1 ++ (l2 ++ l3))
++Assoc nil l2 l3 = refl
++Assoc (x :: l1) l2 l3 rewrite ++Assoc l1 l2 l3 = refl

-- This is the one from the Coq standard library. It represents
-- permutations as a sequence of individual swaps.
-- http://coq.inria.fr/stdlib/Coq.Sorting.Permutation.html
data _><_ {X : Set} : List X -> List X -> Set where
  permNil   : nil >< nil
  permSkip  : forall {x l1 l2}  -> l1 >< l2 -> (x :: l1) >< (x :: l2)
  permSwap  : forall {x y l}    ->           (x :: y :: l) >< (y :: x :: l)
  permTrans : forall {l1 l2 l3} -> l1 >< l2 -> l2 >< l3 -> l1 >< l3

permRefl : forall {X : Set} (l : List X) -> l >< l
permRefl nil      = permNil
permRefl (x :: l) = permSkip (permRefl l)

permAppL : {X : Set} -> {l1 l2 l : List X} -> l1 >< l2 -> (l1 ++ l) >< (l2 ++ l)
permAppL permNil           = permRefl _
permAppL (permSkip p)      = permSkip (permAppL p)
permAppL permSwap          = permSwap
permAppL (permTrans p1 p2) = permTrans (permAppL p1) (permAppL p2)

permAppR : {X : Set} -> (l : List X) -> {l1 l2 : List X} -> l1 >< l2 -> (l ++ l1) >< (l ++ l2)
permAppR nil      p = p
permAppR (x :: l) p = permSkip (permAppR l p)

nilPerm : {X : Set} -> {K  : List X} -> nil >< K -> K == nil
nilPerm permNil = refl
nilPerm (permTrans p1 p2) rewrite nilPerm p1 = nilPerm p2

singlPerm : {X : Set} -> {l : List X} {x : X} -> (x :: nil) >< l -> l == x :: nil
singlPerm (permSkip p) rewrite nilPerm p = refl
singlPerm (permTrans p1 p2) rewrite singlPerm p1 = singlPerm p2

permSymm : {X : Set} -> {l1 l2 : List X} -> l1 >< l2 -> l2 >< l1
permSymm permNil           = permNil
permSymm (permSkip p)      = permSkip (permSymm p)
permSymm permSwap          = permSwap
permSymm (permTrans p1 p2) = permTrans (permSymm p2) (permSymm p1)

permBubble : {X : Set} -> (l1 l2 : List X) {x : X} -> (x :: l1 ++ l2) >< (l1 ++ (x :: l2))
permBubble nil       l2 = permRefl _
permBubble (y :: l1) l2 = permTrans permSwap (permSkip (permBubble l1 l2))

permAssoc : {X : Set} -> (l1 l2 l3 : List X) -> ((l1 ++ l2) ++ l3) >< (l1 ++ (l2 ++ l3))
permAssoc l1 l2 l3 rewrite ++Assoc l1 l2 l3 = permRefl _

permSwap++ : {X : Set} -> (l1 l2 : List X) -> (l1 ++ l2) >< (l2 ++ l1)
permSwap++ nil       l2 rewrite ++nil l2 = permRefl l2
permSwap++ (x :: l1) l2 = permTrans (permSkip (permSwap++ l1 l2)) (permBubble l2 l1)

zip : forall {a b c} {A : Set a} {B : Set b} {C : Set c} ->
      (A -> B -> C) -> List A -> List B -> List C
zip f nil nil = nil
zip f nil (b :: bs) = nil
zip f (a :: as) nil = nil
zip f (a :: as) (b :: bs) = f a b :: zip f as bs

data _elem_ {x} {X : Set x} (x : X) : List X -> Set where
  here : forall {l} -> x elem (x :: l)
  there : forall {l y} -> x elem l -> x elem (y :: l)

index : forall {x} {X : Set x} {x : X} {l} -> x elem l -> Nat
index here = zero
index (there e) = succ (index e)

Ctx : Set
Ctx = List LTy

data All {x p} {X : Set x} (P : X -> Set p) : List X -> Set (x ⊔ p) where
  nil : All P nil
  _::_ : forall {x l} (p : P x) (ps : All P l) -> All P (x :: l)

_++All_ : forall {x p} {X : Set x} {P : X -> Set p} {l0 l1 : List X} ->
          All P l0 -> All P l1 -> All P (l0 ++ l1)
nil ++All qs = qs
(p :: ps) ++All qs = p :: (ps ++All qs)

mapAll : forall {x p q} {X : Set x} {P : X -> Set p} {Q : X -> Set q} {l : List X} ->
         (forall {x} -> P x -> Q x) -> All P l -> All Q l
mapAll f nil = nil
mapAll f (p :: ps) = f p :: mapAll f ps

zipAll : forall {x p q r} {X : Set x} {P : X -> Set p} {Q : X -> Set q} {R : X -> Set r}
                {l : List X} ->
         (forall {x} -> P x -> Q x -> R x) ->
         All P l -> All Q l -> All R l
zipAll f nil nil = nil
zipAll f (p :: ps) (q :: qs) = f p q :: zipAll f ps qs

allTags : forall {x y} {X : Set x} {Y : Set y} {l : List X} -> All (\ _ -> Y) l -> List Y
allTags nil = nil
allTags (y :: ys) = y :: allTags ys

allTagsInj : forall {x y} {X : Set x} {Y : Set y} {l : List X} {ps qs : All (\ _ -> Y) l} ->
             allTags ps == allTags qs -> ps == qs
allTagsInj {ps = nil} {nil} eq = refl
allTagsInj {ps = p :: ps} {q :: qs} eq with ::Inj eq
... | pq , psqs = cong2 _::_ pq (allTagsInj psqs)

zipAll-zip : forall {x a b c} {X : Set x} {A : Set a} {B : Set b} {C : Set c}
             (f : A -> B -> C) {xs : List X} (ps : All (\ _ -> A) xs) (qs : All (\ _ -> B) xs) ->
             allTags (zipAll f ps qs) == zip f (allTags ps) (allTags qs)
zipAll-zip f nil nil = refl
zipAll-zip f (p :: ps) (q :: qs) = cong2 _::_ refl (zipAll-zip f ps qs)

All::Inj : forall {x p} {X : Set x} {P : X -> Set p}
           {x : X} {l : List X} {p p' : P x} {ps ps' : All P l} ->
           _==_ {A = All P (x :: l)} (p :: ps) (p' :: ps') -> (p == p') * (ps == ps')
All::Inj refl = refl , refl

==All? : forall {x p} {X : Set x} {P : X -> Set p} {l : List X} ->
         (forall {x} -> DecEq (P x)) -> DecEq (All P l)
==All? eq? nil nil = yes refl
==All? eq? (p :: ps) (q :: qs) with eq? p q
==All? eq? (p :: ps) (.p :: qs) | yes refl with ==All? eq? ps qs
==All? eq? (p :: ps) (.p :: .ps) | yes refl | yes refl = yes refl
==All? eq? (p :: ps) (.p :: qs) | yes refl | no np = no (np o snd o All::Inj)
==All? eq? (p :: ps) (q :: qs) | no np = no (np o fst o All::Inj)

-- assign a boolean to each element of a list
{-+}
Partition : forall {X} -> List X -> Set
Partition l = (Sg _ \ x -> x elem l) -> Two

emptyPartition : forall {X} {l : List X} -> Partition l
emptyPartition = \ _ -> ff

singlPartition : forall {X} {x : X} {l} -> x elem l -> Partition l
singlPartition e1 (_ , e2) = floor (index e1 ==Nat? index e2)
{+-}

{--}
Partition : forall {x} {X : Set x} -> List X -> Set x
Partition = All (\ _ -> Two)

emptyPartition : forall {x} {X : Set x} {l : List X} -> Partition l
emptyPartition {l = nil} = nil
emptyPartition {l = x :: l} = ff :: emptyPartition

singlPartition : forall {x} {X : Set x} {x : X} {l} -> x elem l -> Partition l
singlPartition here = tt :: emptyPartition
singlPartition (there e) = ff :: singlPartition e

fullPartition : forall {x} {X : Set x} {l : List X} -> Partition l
fullPartition = mapAll (\ _ -> tt) emptyPartition
{--}

data Zip {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r)
         : List A -> List B -> Set (a ⊔ b ⊔ r) where
  nil : Zip R nil nil
  _::_ : forall {a b as bs} -> R a b -> Zip R as bs -> Zip R (a :: as) (b :: bs)

List== : forall {x} {X : Set x} {l0 l1 : List X} -> Zip _==_ l0 l1 -> l0 == l1
List== nil = refl
List== (eq :: eqs) = cong2 _::_ eq (List== eqs)

==Zip : forall {x} {X : Set x} {l l' : List X} -> l == l' -> Zip _==_ l l
==Zip {l = nil} eq = nil
==Zip {l = x :: l} eq = refl :: ==Zip refl