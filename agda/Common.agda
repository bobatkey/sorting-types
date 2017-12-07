module Common where

open import Base public

id : forall {l} {A : Set l} -> A -> A
id x = x

infixr 5 _o_
_o_ : forall {a b c} {A : Set a} {B : A -> Set b} {C : forall {a} -> B a -> Set c}
      (f : forall {a} (b : B a) -> C b) (g : forall a -> B a) a -> C (g a)
(f o g) x = f (g x)

case_return_of_ :
  forall {a b} {A : Set a} (x : A) (B : A -> Set b) -> (forall x -> B x) -> B x
case x return B of f = f x

case_of_ : forall {a b} {A : Set a} {B : Set b} (x : A) -> (A -> B) -> B
case x of f = f x

infixr 1 _=[_]=_
infixr 2 _QED

_=[_]=_ : forall {a} {A : Set a} (x : A) {y z} -> x == y -> y == z -> x == z
x =[ xy ]= yz = trans xy yz

_QED : forall {a} {A : Set a} (x : A) -> x == x
x QED = refl

record Lift {a l} (A : Set a) : Set (a ⊔ l) where
  constructor lift
  field
    lower : A
open Lift public

data Zero : Set where

Zero-elim : forall {l} {A : Set l} -> Zero -> A
Zero-elim ()

Not : forall {a} -> Set a -> Set a
Not A = A -> Zero

aboutZero : forall {p} (P : Zero -> Set p) {x} -> P x
aboutZero P {()}

infix 0 _/=_
_/=_ : forall {a} {A : Set a} -> A -> A -> Set a
x /= y = Not (x == y)

infixr 1 -,_
record Sgi {a b} (A : Set a) (B : A -> Set b) : Set (a ⊔ b) where
  constructor -,_
  field
    {fsti} : A
    sndi : B fsti
open Sgi

mapSgi : forall {a b b'} {A : Set a} {B : A -> Set b} {B' : A -> Set b'} ->
         (forall {a} -> B a -> B' a) -> Sgi A B -> Sgi A B'
mapSgi f (-, b) = -, f b

infixl 4 _<-$>_
_<-$>_ = mapSgi

uncurryi : forall {a b c} {A : Set a} {B : A -> Set b} {C : (a : A) -> B a -> Set c} ->
           ({a : A} (b : B a) -> C a b) -> (ab : Sgi A B) -> C (fsti ab) (sndi ab)
uncurryi f (-, b) = f b

infixl 100 _-$_
_-$_ = uncurryi

record One : Set where
  constructor <>
open One public

record Graph {a b} {A : Set a} {B : A -> Set b} (f : (x : A) -> B x) (x : A) (y : B x) : Set (a ⊔ b) where
  constructor ingraph
  field
    eq : f x == y

inspect : forall {a b} {A : Set a} {B : A -> Set b} (f : (x : A) -> B x) (x : A) -> Graph f x (f x)
inspect f x = ingraph refl

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

if_return_then_else_ : forall {a} (x : Two) (A : Two -> Set a) -> A tt -> A ff -> A x
if tt return A then t else f = t
if ff return A then t else f = f

if_then_else_ : forall {a} {A : Set a} -> Two -> A -> A -> A
if x then t else f = if x return _ then t else f

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

infixr 1 _⊎_
data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inl : (a : A) -> A ⊎ B
  inr : (b : B) -> A ⊎ B

map⊎ : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : Set b} {B' : Set b'} ->
       (A -> A') -> (B -> B') -> A ⊎ B -> A' ⊎ B'
map⊎ f g (inl a) = inl (f a)
map⊎ f g (inr b) = inr (g b)

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

byDec : forall {x X} (X? : Dec {x} X) {auto : Auto X?} -> X
byDec X? {auto} = toWitness auto

DecEq : forall {x} -> Set x -> Set x
DecEq X = (x y : X) -> Dec (x == y)

IfYes : forall {x l X} -> Dec {x} X -> (X -> Set l) -> Set l
IfYes (yes p) P = P p
IfYes (no np) P = Lift One

infixr 4 _>>=[_]_ _<&>[_]_
_>>=[_]_ : forall {a b} {A : Set a} {B : Set b} ->
           Dec A -> (B -> A) -> (A -> Dec B) -> Dec B
yes a >>=[ B->A ] A->B? = A->B? a
no na >>=[ B->A ] A->B? = no (na o B->A)

_<&>[_]_ : forall {a b} {A : Set a} {B : Set b} ->
           Dec A -> (B -> A) -> (A -> B) -> Dec B
A? <&>[ g ] f = mapDec f g A?

_==Two?_ : DecEq Two
tt ==Two? tt = yes refl
tt ==Two? ff = no (λ ())
ff ==Two? tt = no (λ ())
ff ==Two? ff = yes refl

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

infixr 6 _+N_
_+N_ : Nat -> Nat -> Nat
zero   +N n = n
succ m +N n = succ (m +N n)

+N-zero : forall m -> m +N zero == m
+N-zero zero = refl
+N-zero (succ m) = cong succ (+N-zero m)

+N-succ : forall m n -> m +N succ n == succ (m +N n)
+N-succ zero n = refl
+N-succ (succ m) n = cong succ (+N-succ m n)

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

data _<=_ : Nat -> Nat -> Set where
  z<=n : forall {n} -> zero <= n
  s<=s : forall {m n} -> m <= n -> succ m <= succ n

_<_ : Nat -> Nat -> Set
m < n = succ m <= n

_<=?_ : forall m n -> Dec (m <= n)
zero <=? n = yes z<=n
succ m <=? zero = no \ ()
succ m <=? succ n = mapDec s<=s (\ { (s<=s le) -> le }) (m <=? n)

_<?_ : forall m n -> Dec (m < n)
m <? n = succ m <=? n

_*?_ : forall {a b A B} -> Dec {a} A -> Dec {b} B -> Dec (A * B)
_*?_ (yes a) (yes b) = yes (a , b)
_*?_ (yes a) (no nb) = no (\ { (_ , b) -> nb b })
_*?_ (no na) B? = no (\ { (a , b) -> na a })

==* : forall {a b A B} {p q : _*_ {a} {b} A B} -> p == q -> (fst p == fst q) * (snd p == snd q)
==* refl = refl , refl

data Fin : Nat -> Set where
  zero : forall {n} -> Fin (succ n)
  succ : forall {n} -> Fin n -> Fin (succ n)

from< : forall {m n} -> m < n -> Fin n
from< {zero} (s<=s le) = zero
from< {succ m} (s<=s le) = succ (from< le)

infix 6 #_
#_ : forall {n} m {less : Auto (m <? n)} -> Fin n
#_ m {less} = from< (toWitness less)

infixr 5 _::_ _++_ _+V_

data List {a} (A : Set a) : Set a where
  nil  : List A
  _::_ : A -> List A -> List A

--------------------------------------------------------------------------------
-- Permutations and so on
_++_ : forall {x} {X : Set x} -> List X -> List X -> List X
nil       ++ l2 = l2
(x :: l1) ++ l2 = x :: (l1 ++ l2)

fold : forall {x y} {X : Set x} {Y : Set y} -> Y -> (X -> Y -> Y) -> List X -> Y
fold n c nil = n
fold n c (x :: l) = c x (fold n c l)

length : forall {x X} -> List {x} X -> Nat
length = fold zero \ _ -> succ

mapList : forall {x y X Y} -> (X -> Y) -> List {x} X -> List {y} Y
mapList f nil = nil
mapList f (x :: xs) = f x :: mapList f xs

infix 5 _!!_
_!!_ : forall {x X} (xs : List {x} X) -> Fin (length xs) -> X
nil !! ()
(x :: xs) !! zero = x
(x :: xs) !! succ i = xs !! i

++nil : forall {x} {X : Set x} -> (l : List X) -> l ++ nil == l
++nil nil      = refl
++nil (x :: l) rewrite ++nil l = refl

++Assoc : forall {x} {X : Set x} (l1 l2 l3 : List X) -> ((l1 ++ l2) ++ l3) == (l1 ++ (l2 ++ l3))
++Assoc nil l2 l3 = refl
++Assoc (x :: l1) l2 l3 rewrite ++Assoc l1 l2 l3 = refl

::Inj : forall {a} {A : Set a} {x0 x1 : A} {l0 l1} ->
        x0 :: l0 == x1 :: l1 -> (x0 == x1) * (l0 == l1)
::Inj refl = refl , refl

++==nil : forall {a} {A : Set a} xs {ys : List A} -> xs ++ ys == nil -> (xs == nil) * (ys == nil)
++==nil nil {nil} eq = refl , refl
++==nil nil {x :: ys} ()
++==nil (x :: xs) {ys} ()

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

--------------------------------------------------------------------------------
infixr 30 _-o_
data LTy : Set where
  KEY           : LTy
  LIST          : LTy -> LTy
  _-o_ _<**>_ _&_  : LTy -> LTy -> LTy

data _elem_ {x} {X : Set x} (x : X) : List X -> Set where
  here : forall {l} -> x elem (x :: l)
  there : forall {l y} -> x elem l -> x elem (y :: l)

index : forall {x} {X : Set x} {x : X} {l} -> x elem l -> Nat
index here = zero
index (there e) = succ (index e)

infix 5 _!!Elem_
_!!Elem_ : forall {x X} (xs : List {x} X) i -> (xs !! i) elem xs
nil !!Elem ()
(x :: xs) !!Elem zero = here
(x :: xs) !!Elem succ i = there (xs !!Elem i)

elemSplit : forall {a A x} {xs : List {a} A} -> x elem xs -> List A * List A
elemSplit (here {xs}) = nil , xs
elemSplit (there {_} {y} e) with elemSplit e
... | xs , ys = y :: xs , ys

-- god of the gaps
data Mele {a A} : List {a} A -> Set where
  here : forall {l} -> Mele l
  there : forall {x l} -> Mele l -> Mele (x :: l)

insert : forall {a A} {xs : List {a} A} -> A -> Mele xs -> List A
insert x (here {xs}) = x :: xs
insert x (there {y} {ys} m) = y :: insert x m

insertPreservesElem : forall {a A x y xs} (m : Mele {a} {A} xs) ->
                      x elem xs -> x elem insert y m
insertPreservesElem here e = there e
insertPreservesElem (there m) here = here
insertPreservesElem (there m) (there e) = there (insertPreservesElem m e)

Ctx : Set
Ctx = List LTy

--------------------------------------------------------------------------------
-- semantics of types

[[_]]T : LTy -> Set
[[ KEY ]]T      = Nat
[[ LIST T ]]T   = List [[ T ]]T
[[ S -o T ]]T   = [[ S ]]T -> [[ T ]]T
[[ S <**> T ]]T = [[ S ]]T * [[ T ]]T
[[ S & T ]]T    = [[ S ]]T * [[ T ]]T

[[_]]C : Ctx -> Set
[[ nil ]]C    = One
[[ S :: G ]]C = [[ S ]]T * [[ G ]]C

-- different from fold
foldright : {X Y : Set} -> X -> (Y -> (List Y * X) -> X) -> List Y -> X
foldright n c nil       = n
foldright n c (y :: ys) = c y (ys , foldright n c ys)

compare : {X : Set} -> Nat -> Nat -> ((Nat -> Nat -> X) * (Nat -> Nat -> X)) -> X
compare m n (GTE , LT) with compareNat m n
compare m .(succ (m +N k)) (GTE , LT) | lt .m k  = LT (succ (m +N k)) m
compare .(n +N k) n        (GTE , LT) | gte k .n = GTE (n +N k) n

--------------------------------------------------------------------------------
-- Logical Predicates to prove the permutation property

KeySet : Set
KeySet = List Nat

[_|=_contains_] : KeySet -> (T : LTy) -> [[ T ]]T -> Set
[ K |= KEY contains n ]            = (n :: nil) >< K
[ K |= LIST T contains nil ]       = nil >< K
[ K |= LIST T contains (t :: ts) ] = Sg KeySet \ K1 -> Sg KeySet \ K2 -> (K1 ++ K2) >< K * [ K1 |= T contains t ] * [ K2 |= LIST T contains ts ]
[ K |= S -o T contains f ]         = forall K' s -> [ K' |= S contains s ] -> [ K ++ K' |= T contains f s ]
[ K |= S <**> T contains (s , t) ] = Sg KeySet \ K1 -> Sg KeySet \ K2 -> (K1 ++ K2) >< K * [ K1 |= S contains s ] * [ K2 |= T contains t ]
[ K |= S & T contains (s , t) ]    = [ K |= S contains s ] * [ K |= T contains t ]

repList : forall K K' -> [ K |= LIST KEY contains K' ] -> K' >< K
repList K nil       phi                           rewrite nilPerm phi    = permRefl nil
repList K (k :: ks) (K1 , K2 , phi , psi1 , psi2) rewrite singlPerm psi1 = permTrans (permSkip (repList _ _ psi2)) phi

listRep : forall K -> [ K |= LIST KEY contains K ]
listRep nil      = permNil
listRep (k :: K) = (k :: nil) , K , permRefl (k :: K) , permRefl (k :: nil) , listRep K

preservePerm : forall {K K'} -> (T : LTy) -> (x : [[ T ]]T) -> K >< K' -> [ K |= T contains x ] -> [ K' |= T contains x ]
preservePerm KEY        n         p prf = permTrans prf p
preservePerm (LIST T)   nil       p phi  = permTrans phi p
preservePerm (LIST T)   (t :: ts) p (K1 , K2 , p' , r1 , r2) = K1 , K2 , permTrans p' p , r1 , r2
preservePerm (S -o T)   f         p prf = \ K' s x -> preservePerm T (f s) (permAppL p) (prf K' s x)
preservePerm (S <**> T) (s , t)   p (K1 , K2 , p' , r1 , r2) = K1 , K2 , permTrans p' p , r1 , r2
preservePerm (S & T)    (s , t)   p (r1 , r2) = preservePerm S s p r1 , preservePerm T t p r2

lem-1 : forall {A : Set} -> (l0 l1 l2 : List A) -> ((l2 ++ l0) ++ l1) >< ((l0 ++ l1) ++ l2)
lem-1 l0 l1 l2 = permTrans (permAppL (permSwap++ l2 l0))
                           (permTrans (permAssoc l0 l2 l1)
                                      (permTrans (permAppR l0 (permSwap++ l2 l1))
                                                 (permSymm (permAssoc l0 l1 l2))))

lem-2 : forall {A : Set} -> (l0 l1 l2 : List A) -> ((l2 ++ l1) ++ l0) >< ((l0 ++ l1) ++ l2)
lem-2 l0 l1 l2 = permTrans (permAppL (permSwap++ l2 l1)) (permTrans (permSwap++ (l1 ++ l2) l0) (permSymm (permAssoc l0 l1 l2)))

--------------------------------------------------------------------------------
-- resource annotations to contexts

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

mapAllD : forall {x y p q} {X : Set x} {Y : Set y} {P : X -> Set p} {Q : Y -> Set q}
          {l : List X} (f : X -> Y) -> (forall {x} -> P x -> Q (f x)) ->
          All P l -> All Q (mapList f l)
mapAllD f g nil = nil
mapAllD f g (p :: ps) = g p :: mapAllD f g ps

zipAll : forall {x p q r} {X : Set x} {P : X -> Set p} {Q : X -> Set q} {R : X -> Set r}
                {l : List X} ->
         (forall {x} -> P x -> Q x -> R x) ->
         All P l -> All Q l -> All R l
zipAll f nil nil = nil
zipAll f (p :: ps) (q :: qs) = f p q :: zipAll f ps qs

allTags : forall {x y} {X : Set x} {Y : Set y} {l : List X} -> All (\ _ -> Y) l -> List Y
allTags nil = nil
allTags (y :: ys) = y :: allTags ys

allTagsLength : forall {x y} {X : Set x} {Y : Set y} {xs : List X}
                (ys : All (\ _ -> Y) xs) -> length (allTags ys) == length xs
allTagsLength nil = refl
allTagsLength (y :: ys) = cong succ (allTagsLength ys)

takeDropAll : forall {x p} {X : Set x} {P : X -> Set p} l0 {l1 : List X} ->
              All P (l0 ++ l1) -> All P l0 * All P l1
takeDropAll nil ps = nil , ps
takeDropAll (x :: l0) (p :: ps) with takeDropAll l0 ps
... | pxs , pys = p :: pxs , pys

++All-takeDropAll : forall {x p} {X : Set x} {P : X -> Set p} l0 {l1 : List X}
                    (ps : All P (l0 ++ l1)) -> uncurry _++All_ (takeDropAll l0 ps) == ps
++All-takeDropAll nil ps = refl
++All-takeDropAll (x :: l0) (p :: ps) = cong (p ::_) (++All-takeDropAll l0 ps)

takeDropAll-++All : forall {x p} {X : Set x} {P : X -> Set p} {xs ys}
                    (pxs : All P xs) (pys : All P ys) ->
                    takeDropAll xs (pxs ++All pys) == (pxs , pys)
takeDropAll-++All nil pys = refl
takeDropAll-++All (p :: pxs) pys rewrite takeDropAll-++All pxs pys = refl

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

::AllInj : forall {x p} {X : Set x} {P : X -> Set p}
           {x : X} {l : List X} {p p' : P x} {ps ps' : All P l} ->
           _==_ {A = All P (x :: l)} (p :: ps) (p' :: ps') -> (p == p') * (ps == ps')
::AllInj refl = refl , refl

++AllInj : forall {x p} {X : Set x} {P : X -> Set p}
           {xs ys : List X} (pxs pxs' : All P xs) {pys pys' : All P ys} ->
           (pxs ++All pys) == (pxs' ++All pys') -> (pxs == pxs') * (pys == pys')
++AllInj nil nil eq = refl , eq
++AllInj (px :: pxs) (px' :: pxs') eq with ::AllInj eq
... | pxeq , pseq with ++AllInj pxs pxs' pseq
...   | pxseq , pyseq = cong2 _::_ pxeq pxseq , pyseq

==All? : forall {x p} {X : Set x} {P : X -> Set p} {l : List X} ->
         (forall {x} -> DecEq (P x)) -> DecEq (All P l)
==All? eq? nil nil = yes refl
==All? eq? (p :: ps) (q :: qs) with eq? p q
==All? eq? (p :: ps) (.p :: qs) | yes refl with ==All? eq? ps qs
==All? eq? (p :: ps) (.p :: .ps) | yes refl | yes refl = yes refl
==All? eq? (p :: ps) (.p :: qs) | yes refl | no np = no (np o snd o ::AllInj)
==All? eq? (p :: ps) (q :: qs) | no np = no (np o fst o ::AllInj)

-- assign a boolean to each element of a list
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

elemSplitAll : forall {a p A P x xs} (e : x elem xs) ->
               All {a} {p} {A} P xs -> uncurry _*_ (map* (All P) (All P) (elemSplit e))
elemSplitAll here (p :: ps) = nil , ps
elemSplitAll (there e) (p :: ps) with elemSplitAll e ps
... | qs , rs = p :: qs , rs

retrieveAll : forall {a p A P x xs} -> x elem xs -> All {a} {p} {A} P xs -> P x
retrieveAll here (p :: ps) = p
retrieveAll (there e) (p :: ps) = retrieveAll e ps

data Zip {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r)
         : List A -> List B -> Set (a ⊔ b ⊔ r) where
  nil : Zip R nil nil
  _::_ : forall {a b as bs} (r : R a b) (rs : Zip R as bs) -> Zip R (a :: as) (b :: bs)

List== : forall {x} {X : Set x} {l0 l1 : List X} -> Zip _==_ l0 l1 -> l0 == l1
List== nil = refl
List== (eq :: eqs) = cong2 _::_ eq (List== eqs)

==Zip : forall {x} {X : Set x} {l l' : List X} -> l == l' -> Zip _==_ l l'
==Zip {l = nil} refl = nil
==Zip {l = x :: l} refl = refl :: ==Zip refl

zipLength : forall {a b r A B R xs ys} ->
            Zip {a} {b} {r} {A} {B} R xs ys -> length xs == length ys
zipLength nil = refl
zipLength (r :: rs) = cong succ (zipLength rs)

infix 4 _≤th_ _<th_ _≤th?_ _<th?_
-- thinnings
data _≤th_ : Nat -> Nat -> Set where
  oz : zero ≤th zero
  os : forall {m n} -> m ≤th n -> succ m ≤th succ n
  o' : forall {m n} -> m ≤th n -> m ≤th succ n

≤th-refl : forall m -> m ≤th m
≤th-refl zero = oz
≤th-refl (succ m) = os (≤th-refl m)

z≤th : forall n -> zero ≤th n
z≤th zero = oz
z≤th (succ x) = o' (z≤th x)

zeroth : forall {n} -> 1 ≤th succ n
zeroth = os (z≤th _)

<th⇒≤th : forall {x y} -> succ x ≤th y -> x ≤th y
<th⇒≤th (os th) = o' th
<th⇒≤th (o' th) = o' (<th⇒≤th th)

op : forall {x y} -> succ x ≤th succ y -> x ≤th y
op (os th) = th
op (o' th) = <th⇒≤th th

z≤th-unique : forall {n} (th th' : zero ≤th n) -> th == th'
z≤th-unique oz oz = refl
z≤th-unique (o' th) (o' th') = cong o' (z≤th-unique th th')

osInj : forall {m n} {th th' : m ≤th n} -> os th == os th' -> th == th'
osInj refl = refl
o'Inj : forall {m n} {th th' : m ≤th n} -> o' th == o' th' -> th == th'
o'Inj refl = refl

_==th?_ : forall {m n} (th th' : m ≤th n) -> Dec (th == th')
oz ==th? oz = yes refl
os th ==th? os th' = mapDec (cong os) osInj (th ==th? th')
os th ==th? o' th' = no \ ()
o' th ==th? os th' = no \ ()
o' th ==th? o' th' = mapDec (cong o') o'Inj (th ==th? th')

_≤th?_ : forall x y -> Dec (x ≤th y)
zero ≤th? y = yes (z≤th _)
succ x ≤th? zero = no \ ()
succ x ≤th? succ y = mapDec os op (x ≤th? y)

_<th_ : (x y : Nat) -> Set
x <th y = succ x ≤th y

_<th?_ : forall x y -> Dec (x <th y)
x <th? y = succ x ≤th? y

1≤th-from-<th : forall {m n} -> m <th n -> 1 ≤th n
1≤th-from-<th {m} {zero} ()
1≤th-from-<th {zero} {succ n} th = zeroth
1≤th-from-<th {succ m} {succ n} th = o' (1≤th-from-<th {m} {n} (op th))

infix 6 #th_
#th_ : forall {n} m {less : Auto (m <th? n)} -> 1 ≤th n
#th_ {n} m {less} = 1≤th-from-<th (toWitness {X? = m <th? n} less)

1≤thToNat : forall {m} -> 1 ≤th m -> Nat
1≤thToNat (os i) = zero
1≤thToNat (o' i) = succ (1≤thToNat i)

punchOut : forall {n} {i j : 1 ≤th succ n} -> i /= j -> 1 ≤th n
punchOut {n} {os i} {os j} neq = Zero-elim (neq (cong os (z≤th-unique i j)))
punchOut {n} {os i} {o' j} neq = j
punchOut {zero} {o' ()} {j} neq
punchOut {succ n} {o' i} {os j} neq = zeroth
punchOut {succ n} {o' i} {o' j} neq = o' (punchOut (neq o cong o'))

punchIn : forall {n} -> 1 ≤th succ n -> 1 ≤th n -> 1 ≤th succ n
punchIn (os i) j = o' j
punchIn (o' i) (os j) = zeroth
punchIn (o' i) (o' j) = o' (punchIn i j)

1≤th-split : forall {m} -> 1 ≤th succ m -> Sg _ \ n -> Sg _ \ o -> n +N o == m
1≤th-split {m} (os i) = zero , m , refl
1≤th-split {zero} (o' i) = zero , zero , refl
1≤th-split {succ m} (o' i) = mapSg succ (mapSg id (cong succ)) (1≤th-split i)

1≤th-part : forall m {n} -> 1 ≤th m +N n -> 1 ≤th m ⊎ 1 ≤th n
1≤th-part zero i = inr i
1≤th-part (succ m) (os i) = inl zeroth
1≤th-part (succ m) (o' i) = map⊎ o' id (1≤th-part m i)

1≤th-leftPart : forall {m} n -> 1 ≤th m -> 1 ≤th m +N n
1≤th-leftPart n (os i) = zeroth
1≤th-leftPart n (o' i) = o' (1≤th-leftPart n i)

1≤th-rightPart : forall m {n} -> 1 ≤th n -> 1 ≤th m +N n
1≤th-rightPart zero i = i
1≤th-rightPart (succ m) i = o' (1≤th-rightPart m i)

1≤th-join : forall m {n} -> 1 ≤th m ⊎ 1 ≤th n -> 1 ≤th m +N n
1≤th-join m (inl i) = 1≤th-leftPart _ i
1≤th-join m (inr i) = 1≤th-rightPart m i

1≤th-part-toNat :
  forall m {n} (i : 1 ≤th m +N n) ->
  case 1≤th-part m i of \
  { (inl jm) -> 1≤thToNat i == 1≤thToNat jm
  ; (inr jn) -> 1≤thToNat i == m +N 1≤thToNat jn
  }
1≤th-part-toNat zero i = refl
1≤th-part-toNat (succ m) (os i) = refl
1≤th-part-toNat (succ m) (o' i) with 1≤th-part m i | 1≤th-part-toNat m i
1≤th-part-toNat (succ m) (o' i) | inl _ | r = cong succ r
1≤th-part-toNat (succ m) (o' i) | inr _ | r = cong succ r

punchOutN : forall m {n} (i : 1 ≤th m +N succ n) -> 1≤thToNat i /= m -> 1 ≤th m +N n
punchOutN zero (os i) neq = Zero-elim (neq refl)
punchOutN zero (o' i) neq = i
punchOutN (succ m) (os i) neq = zeroth
punchOutN (succ m) (o' i) neq = o' (punchOutN m i (neq o cong succ))
--punchOutN m i neq with 1≤th-part m i | 1≤th-part-toNat m i
--... | inl jm | _ = 1≤th-leftPart _ jm
--... | inr (os _) | eq rewrite +N-zero m = Zero-elim (neq eq)
--... | inr (o' jn) | _ = 1≤th-rightPart m jn

punchInNMany : forall {m} l n -> (i : 1 ≤th l +N m) -> 1 ≤th l +N n +N m
punchInNMany l n i = 1≤th-join l (map⊎ id (1≤th-rightPart n) (1≤th-part l i))

--punchOutN-toNat :
--  punchOutN m i neq ==
--    case 1≤th-part m i of \
--    { (inl )
--    ;
--    }

data Vec {a} (A : Set a) : Nat -> Set a where
  nil : Vec A zero
  _::_ : forall {n} (x : A) (xs : Vec A n) -> Vec A (succ n)

_+V_ : forall {a A m n} -> Vec {a} A m -> Vec A n -> Vec A (m +N n)
nil +V ys = ys
(x :: xs) +V ys = x :: xs +V ys

headVec : forall {a A n} -> Vec {a} A (succ n) -> A
headVec (x :: xs) = x

tailVec : forall {a A n} -> Vec {a} A (succ n) -> Vec A n
tailVec (x :: xs) = xs

takeVec : forall {a A} m {n} -> Vec {a} A (m +N n) -> Vec A m
takeVec zero xs = nil
takeVec (succ m) (x :: xs) = x :: takeVec m xs

dropVec : forall {a A} m {n} -> Vec {a} A (m +N n) -> Vec A n
dropVec zero xs = xs
dropVec (succ m) (x :: xs) = dropVec m xs

replicateVec : forall {a A} n -> A -> Vec {a} A n
replicateVec zero x = nil
replicateVec (succ n) x = x :: replicateVec n x

1≤th-tabulate : forall {a A m} -> (1 ≤th m -> A) -> Vec {a} A m
1≤th-tabulate {m = zero} f = nil
1≤th-tabulate {m = succ m} f = f zeroth :: 1≤th-tabulate {m = m} (f o o')

1≤th-index : forall {a A m} -> 1 ≤th m -> Vec {a} A m -> A
1≤th-index (os th) (x :: xs) = x
1≤th-index (o' th) (x :: xs) = 1≤th-index th xs

1≤th-splitVec : forall {a A m} i (xs : Vec {a} A m) ->
                let n , o , eq = 1≤th-split i in
                Sg _ \ ys -> Sg _ \ zs -> subst (Vec A) eq (_+V_ {m = n} ys zs) == xs
1≤th-splitVec (os i) xs = nil , xs , refl
1≤th-splitVec (o' i) nil = nil , nil , refl
1≤th-splitVec (o' i) (x :: xs) with 1≤th-split i | 1≤th-splitVec i xs
1≤th-splitVec (o' i) (x :: .(ys +V zs))
  | n , o , refl | ys , zs , refl = x :: ys , zs , refl

1≤th-insertVec : forall {a A m} (i : 1 ≤th succ m) (x : A) (xs : Vec {a} A m) -> Vec A (succ m)
--1≤th-insertVec i x xs with 1≤th-split i | 1≤th-splitVec i xs
--... | n , o , refl | ys , zs , _ = subst (Vec _) (+N-succ n o) (ys +V x :: zs)
1≤th-insertVec (os i) x xs = x :: xs
1≤th-insertVec (o' i) x nil = x :: nil
1≤th-insertVec (o' i) x (x' :: xs) = x' :: 1≤th-insertVec i x xs

1≤th-removeVec : forall {a A m} -> 1 ≤th succ m -> Vec {a} A (succ m) -> Vec A m
1≤th-removeVec (os i) (x :: xs) = xs
1≤th-removeVec {m = zero} (o' ()) (x :: xs)
1≤th-removeVec {m = succ m} (o' i) (x :: xs) = x :: 1≤th-removeVec i xs

1≤th-index-punchIn-insertVec :
  forall {a A m} (i : 1 ≤th succ m) (j : 1 ≤th m) (x : A) (xs : Vec {a} A m) ->
  1≤th-index (punchIn i j) (1≤th-insertVec i x xs) == 1≤th-index j xs
1≤th-index-punchIn-insertVec (os i) j x xs = refl
1≤th-index-punchIn-insertVec (o' i) (os j) x (x' :: xs) = refl
1≤th-index-punchIn-insertVec (o' i) (o' j) x (x' :: xs) =
  1≤th-index-punchIn-insertVec i j x xs

1≤th-index-insertVec : forall {a A m} (i : 1 ≤th succ m) (x : A) (xs : Vec {a} A m) ->
                       1≤th-index i (1≤th-insertVec i x xs) == x
1≤th-index-insertVec (os i) x xs = refl
1≤th-index-insertVec (o' ()) x nil
1≤th-index-insertVec (o' i) x (x' :: xs) = 1≤th-index-insertVec i x xs

1≤th-index-/=-insertVec :
  forall {a A m} {i j : 1 ≤th succ m}
  (neq : i /= j) (x : A) (xs : Vec {a} A m) ->
  1≤th-index j (1≤th-insertVec i x xs) == 1≤th-index (punchOut neq) xs
1≤th-index-/=-insertVec {i = os i} {os j} neq x xs =
  Zero-elim (neq (cong os (z≤th-unique i j)))
1≤th-index-/=-insertVec {i = os i} {o' j} neq x xs = refl
1≤th-index-/=-insertVec {i = o' ()} {j} neq x nil
1≤th-index-/=-insertVec {i = o' i} {os j} neq x (x' :: xs) = refl
1≤th-index-/=-insertVec {i = o' i} {o' j} neq x (x' :: xs) =
  1≤th-index-/=-insertVec {i = i} {j} _ x xs

1≤th-index-+ :
  forall {a A m n} i (xs : Vec {a} A m) y (zs : Vec A n) ->
  1≤thToNat i == m -> 1≤th-index i (xs +V y :: zs) == y
1≤th-index-+ (os i) nil y zs eq = refl
1≤th-index-+ (o' i) nil y zs ()
1≤th-index-+ (os i) (x :: xs) y zs ()
1≤th-index-+ (o' i) (x :: xs) y zs eq = 1≤th-index-+ i xs y zs (succInj eq)

1≤th-index-part-l :
  forall {a A m n j} (i : 1 ≤th m +N n) (xs : Vec {a} A m) (ys : Vec A n) ->
  1≤th-part m i == inl j -> 1≤th-index j xs == 1≤th-index i (xs +V ys)
1≤th-index-part-l i nil ys ()
1≤th-index-part-l (os i) (x :: xs) ys refl = refl
1≤th-index-part-l {m = succ m} (o' i) (x :: xs) ys eq
  with 1≤th-part m i | inspect (1≤th-part m) i
1≤th-index-part-l {m = succ m} (o' i) (x :: xs) ys refl | inl j | ingraph eq =
  1≤th-index-part-l i xs ys eq
1≤th-index-part-l {m = succ m} (o' i) (x :: xs) ys () | inr _ | _

1≤th-index-part-r :
  forall {a A m n j} (i : 1 ≤th m +N n) (xs : Vec {a} A m) (ys : Vec A n) ->
  1≤th-part m i == inr j -> 1≤th-index j ys == 1≤th-index i (xs +V ys)
1≤th-index-part-r i nil ys refl = refl
1≤th-index-part-r (os i) (x :: xs) ys ()
1≤th-index-part-r {m = succ m} (o' i) (x :: xs) ys eq
  with 1≤th-part m i | inspect (1≤th-part m) i
1≤th-index-part-r {m = succ m} (o' i) (x :: xs) ys () | inl _ | _
1≤th-index-part-r {m = succ m} (o' i) (x :: xs) ys refl | inr j | ingraph eq =
  1≤th-index-part-r i xs ys eq

1≤th-index-leftPart :
  forall {a A m n} (i : 1 ≤th m) (xs : Vec {a} A m) (ys : Vec A n) ->
  1≤th-index (1≤th-leftPart n i) (xs +V ys) == 1≤th-index i xs
1≤th-index-leftPart (os i) (x :: xs) ys = refl
1≤th-index-leftPart (o' i) (x :: xs) ys = 1≤th-index-leftPart i xs ys

1≤th-index-rightPart :
  forall {a A m n} (i : 1 ≤th n) (xs : Vec {a} A m) (ys : Vec A n) ->
  1≤th-index (1≤th-rightPart m i) (xs +V ys) == 1≤th-index i ys
1≤th-index-rightPart i nil ys = refl
1≤th-index-rightPart i (x :: xs) ys = 1≤th-index-rightPart i xs ys

1≤th-index-punchInNMany :
  forall {a A m l n} (ls : Vec A l) (ns : Vec A n) (ms : Vec {a} A m) i ->
  1≤th-index (punchInNMany l n i) (ls +V ns +V ms) == 1≤th-index i (ls +V ms)
1≤th-index-punchInNMany {l = l} {n} ls ns ms i
  with 1≤th-part l i | inspect (1≤th-part l) i
... | inl j | ingraph eq = trans (1≤th-index-leftPart j ls (ns +V ms))
                                 (1≤th-index-part-l i ls ms eq)
... | inr j | ingraph eq =
  trans (1≤th-index-rightPart (1≤th-rightPart n j) ls (ns +V ms))
        (trans (1≤th-index-rightPart j ns ms)
               (1≤th-index-part-r i ls ms eq))

1≤th-index-== :
  forall {a A m} i j (xs : Vec {a} A m) ->
  1≤thToNat i == 1≤thToNat j -> 1≤th-index i xs == 1≤th-index j xs
1≤th-index-== (os i) (os j) (x :: xs) eq = refl
1≤th-index-== (os i) (o' j) xs ()
1≤th-index-== (o' i) (os j) xs ()
1≤th-index-== (o' i) (o' j) (x :: xs) eq = 1≤th-index-== i j xs (succInj eq)

1≤th-index-==l :
  forall {a A m n} i j (xs : Vec {a} A m) (ys : Vec A n) ->
  1≤thToNat i == 1≤thToNat j -> 1≤th-index i xs == 1≤th-index j (xs +V ys)
1≤th-index-==l (os i) (os j) (x :: xs) ys eq = refl
1≤th-index-==l (os i) (o' j) (x :: xs) ys ()
1≤th-index-==l (o' i) (os j) (x :: xs) ys ()
1≤th-index-==l (o' i) (o' j) (x :: xs) ys eq = 1≤th-index-==l i j xs ys (succInj eq)

1≤th-index-==r :
  forall {a A m n} i j (xs : Vec {a} A m) (ys : Vec A n) ->
  m +N 1≤thToNat i == 1≤thToNat j -> 1≤th-index i ys == 1≤th-index j (xs +V ys)
1≤th-index-==r i j nil ys eq = 1≤th-index-== i j ys eq
1≤th-index-==r i (os j) (x :: xs) ys ()
1≤th-index-==r i (o' j) (x :: xs) ys eq = 1≤th-index-==r i j xs ys (succInj eq)

1≤th-index-punchOutN :
  forall {a A m n} i (neq : 1≤thToNat i /= m)
  (xs : Vec {a} A m) y (zs : Vec A n) ->
  1≤th-index (punchOutN m i neq) (xs +V zs) == 1≤th-index i (xs +V y :: zs)
1≤th-index-punchOutN (os i) neq nil y zs = Zero-elim (neq refl)
1≤th-index-punchOutN (o' i) neq nil y zs = refl
1≤th-index-punchOutN (os i) neq (x :: xs) y zs = refl
1≤th-index-punchOutN (o' i) neq (x :: xs) y zs =
  1≤th-index-punchOutN i (neq o cong succ) xs y zs
--1≤th-index-punchOutN {m = m} {n} i neq xs y zs with 1≤th-part m i | 1≤th-part-toNat m i
--... | inl jm | eq rewrite 1≤th-index-leftPart jm xs zs =
--  1≤th-index-==l jm i xs (y :: zs) (sym eq)
--... | inr (os jn) | eq rewrite +N-zero m = Zero-elim (neq eq)
--... | inr (o' jn) | eq rewrite 1≤th-index-rightPart jn xs zs
--                             | +N-succ m (1≤thToNat jn) =
--  {!1≤th-index-==r jn (subst (1 ≤th_) (+N-succ m n) i) xs!}

1≤th->-:: : forall {a} {A : Set a} {m} ->
            A -> (1 ≤th m -> A) -> 1 ≤th succ m -> A
1≤th->-:: x f (os i) = x
1≤th->-:: x f (o' i) = f i

thickenVec : forall {a A m n} -> m ≤th n -> Vec {a} A n -> Vec A m
thickenVec oz nil = nil
thickenVec (os th) (x :: xs) = x :: thickenVec th xs
thickenVec (o' th) (x :: xs) = thickenVec th xs

LengthedList : forall {a} -> Set a -> Nat -> Set a
LengthedList A n = Sg (List A) \ xs -> length xs == n

Vec->LengthedList : forall {a A n} -> Vec {a} A n -> LengthedList A n
Vec->LengthedList nil = nil , refl
Vec->LengthedList (x :: xs) with Vec->LengthedList xs
... | ys , eq = x :: ys , cong succ eq

LengthedList->Vec : forall {a A n} -> LengthedList {a} A n -> Vec A n
LengthedList->Vec (nil , refl) = nil
LengthedList->Vec {n = zero} (x :: xs , ())
LengthedList->Vec {n = succ n} (x :: xs , eq) = x :: LengthedList->Vec (xs , succInj eq)

thickenLengthedList : forall {a A m n} -> m ≤th n -> LengthedList {a} A n -> LengthedList A m
thickenLengthedList th = Vec->LengthedList o thickenVec th o LengthedList->Vec

thickenList : forall {a A m} (xs : List {a} A) -> m ≤th length xs -> List A
thickenList xs th = fst (thickenLengthedList th (xs , refl))

elemSplitThinnings : forall {a A x} {xs : List {a} A} (e : x elem xs) ->
                     let ys , zs = elemSplit e in
                     (length ys ≤th length xs) * (length zs ≤th length xs)
elemSplitThinnings here = z≤th _ , o' (≤th-refl _)
elemSplitThinnings (there e) with elemSplitThinnings e
... | yth , zth = os yth , o' zth

thickenAll : forall {a p A P m xs} (th : m ≤th length xs) ->
             All {a} {p} {A} P xs -> All P (thickenList xs th)
thickenAll oz nil = nil
thickenAll (os th) (p :: ps) = p :: thickenAll th ps
thickenAll (o' th) (p :: ps) = thickenAll th ps

thickenZip : forall {a b r A B R m xs ys} (th : m ≤th length ys)
             (rs : Zip {a} {b} {r} {A} {B} R xs ys) ->
             Zip R (fst (thickenLengthedList th (xs , zipLength rs)))
                   (thickenList ys th)
thickenZip oz nil = nil
thickenZip (os th) (r :: rs)
  rewrite ==IsProp (succInj (cong succ (zipLength rs))) (zipLength rs) =
  r :: thickenZip th rs
thickenZip (o' th) (r :: rs)
  rewrite ==IsProp (succInj (cong succ (zipLength rs))) (zipLength rs) =
  thickenZip th rs

vmap : forall {a b A B n} -> (A -> B) -> Vec {a} A n -> Vec {b} B n
vmap f nil = nil
vmap f (x :: xs) = f x :: vmap f xs

vzip : forall {a b c A B C n} -> (A -> B -> C) ->
       Vec {a} A n -> Vec {b} B n -> Vec {c} C n
vzip f nil ys = nil
vzip f (x :: xs) (y :: ys) = f x y :: vzip f xs ys

1≤th-index-vmap : forall {a b A B n} (i : 1 ≤th n)
                  (f : A -> B) (xs : Vec {a} A n) ->
                  1≤th-index {b} i (vmap f xs) == f (1≤th-index i xs)
1≤th-index-vmap (os i) f (x :: xs) = refl
1≤th-index-vmap (o' i) f (x :: xs) = 1≤th-index-vmap i f xs

1≤th-index-vzip : forall {a b c A B C n} (i : 1 ≤th n)
                  (f : A -> B -> C) (xs : Vec {a} A n) (ys : Vec {b} B n) ->
                  1≤th-index {c} i (vzip f xs ys)
                    == f (1≤th-index i xs) (1≤th-index i ys)
1≤th-index-vzip (os i) f (x :: xs) (y :: ys) = refl
1≤th-index-vzip (o' i) f (x :: xs) (y :: ys) = 1≤th-index-vzip i f xs ys

1≤th-insertVec-vzip :
  forall {a b c A B C n} (i : 1 ≤th succ n) f x y xs ys ->
  1≤th-insertVec {c} {C} i (f x y) (vzip f xs ys) ==
    vzip f (1≤th-insertVec {a} {A} i x xs) (1≤th-insertVec {b} {B} i y ys)
1≤th-insertVec-vzip (os i) f x y xs ys = refl
1≤th-insertVec-vzip (o' i) f x y nil nil = refl
1≤th-insertVec-vzip (o' i) f x y (x' :: xs) (y' :: ys) =
  cong (f x' y' ::_) (1≤th-insertVec-vzip i f x y xs ys)

1≤th-index-replicateVec :
  forall {a A n} (i : 1 ≤th n) x -> 1≤th-index i (replicateVec {a} {A} n x) == x
1≤th-index-replicateVec (os i) x = refl
1≤th-index-replicateVec (o' i) x = 1≤th-index-replicateVec i x

data VZip {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r)
            : forall {n} -> Vec A n -> Vec B n -> Set (a ⊔ b ⊔ r) where
  nil : VZip R nil nil
  _::_ : forall {a b n as bs} (r : R a b) (rs : VZip R {n} as bs)
         -> VZip R (a :: as) (b :: bs)

headVZip : forall {a b r A B R n x xs y ys} ->
           VZip {a} {b} {r} {A} {B} R {succ n} (x :: xs) (y :: ys) -> R x y
headVZip (r :: rs) = r

tailVZip : forall {a b r A B R n x xs y ys} ->
           VZip {a} {b} {r} {A} {B} R {succ n} (x :: xs) (y :: ys) -> VZip R xs ys
tailVZip (r :: rs) = rs

takeVZip : forall {a b r A B R m n xsn ysn} (xsm : Vec A m) (ysm : Vec B m) ->
           VZip {a} {b} {r} {A} {B} R {m +N n} (xsm +V xsn) (ysm +V ysn) -> VZip R xsm ysm
takeVZip nil nil rs = nil
takeVZip (x :: xsm) (y :: ysm) (r :: rs) = r :: takeVZip xsm ysm rs

dropVZip : forall {a b r A B R m n xsn ysn} (xsm : Vec A m) (ysm : Vec B m) ->
           VZip {a} {b} {r} {A} {B} R {m +N n} (xsm +V xsn) (ysm +V ysn) -> VZip R xsn ysn
dropVZip nil nil rs = rs
dropVZip (x :: xsm) (y :: ysm) (r :: rs) = dropVZip xsm ysm rs

==VZip : forall {a A n} {xs ys : Vec {a} A n} -> xs == ys -> VZip _==_ xs ys
==VZip {xs = nil} {nil} eq = nil
==VZip {xs = x :: xs} {.x :: .xs} refl = refl :: ==VZip refl

VZip== : forall {a A n} {xs ys : Vec {a} A n} -> VZip _==_ xs ys -> xs == ys
VZip== nil = refl
VZip== (refl :: eqs) = cong (_ ::_) (VZip== eqs)

headTailVec== : forall {a A n} (xs : Vec {a} A (succ n)) ->
                VZip _==_ (headVec xs :: tailVec xs) xs
headTailVec== (x :: xs) = ==VZip refl

takeDropVec== : forall {a A} m {n} (xs : Vec {a} A (m +N n)) ->
                VZip _==_ (takeVec m xs +V dropVec m xs) xs
takeDropVec== zero xs = ==VZip refl
takeDropVec== (succ m) (x :: xs) = refl :: takeDropVec== m xs

1≤th-tabulate-o : forall {a b A B m} (f : A -> B) (g : 1 ≤th m -> A) ->
                  VZip _==_ (1≤th-tabulate {b} (f o g)) (vmap f (1≤th-tabulate {a} g))
1≤th-tabulate-o {m = zero} f g = nil
1≤th-tabulate-o {m = succ m} f g = refl :: 1≤th-tabulate-o f (g o o')

vmap-+V : forall {a b A B m n} (f : A -> B)
          (xsm : Vec {a} A m) (xsn : Vec A n) ->
          VZip (_==_ {b} {B}) (vmap f (xsm +V xsn)) (vmap f xsm +V vmap f xsn)
vmap-+V f nil xsn = ==VZip refl
vmap-+V f (x :: xsm) xsn = refl :: vmap-+V f xsm xsn

vzip-+V : forall {a b c A B C m n} (f : A -> B -> C)
          (xsm : Vec {a} A m) (ysm : Vec {b} B m) xsn (ysn : Vec B n) ->
          VZip (_==_ {c} {C}) (vzip f (xsm +V xsn) (ysm +V ysn))
                              (vzip f xsm ysm +V vzip f xsn ysn)
vzip-+V f nil nil xsn ysn = ==VZip refl
vzip-+V f (x :: xsm) (y :: ysm) xsn ysn = refl :: vzip-+V f xsm ysm xsn ysn

infixr 5 _+VZip_
_+VZip_ : forall {a b r A B R m n xsm ysm xsn ysn} ->
          VZip R {n = m} xsm ysm -> VZip R {n = n} xsn ysn ->
          VZip {a} {b} {r} {A} {B} R (xsm +V xsn) (ysm +V ysn)
nil +VZip rsn = rsn
(r :: rsm) +VZip rsn = r :: rsm +VZip rsn

replicateVZip :
  forall {a b r A B R} n {x y} -> R x y ->
  VZip {a} {b} {r} {A} {B} R {n} (replicateVec n x) (replicateVec n y)
replicateVZip zero r = nil
replicateVZip (succ n) r = r :: replicateVZip n r

vmap-replicateVec :
  forall {a b A B} f n x ->
  VZip _==_ (vmap {a} {b} {A} {B} f (replicateVec n x)) (replicateVec n (f x))
vmap-replicateVec f zero x = nil
vmap-replicateVec f (succ n) x = refl :: vmap-replicateVec f n x

1≤th-indexVZip : forall {a b r A B R n xs ys} ->
                 (i : 1 ≤th n) ->
                 VZip {a} {b} {r} {A} {B} R {n} xs ys ->
                 R (1≤th-index i xs) (1≤th-index i ys)
1≤th-indexVZip (os i) (r :: rs) = r
1≤th-indexVZip (o' i) (r :: rs) = 1≤th-indexVZip i rs

1≤th-insertVZip : forall {a b r A B R n x y xs ys} ->
                  (i : 1 ≤th succ n) ->
                  R x y -> VZip {a} {b} {r} {A} {B} R {n} xs ys ->
                  VZip R (1≤th-insertVec i x xs) (1≤th-insertVec i y ys)
1≤th-insertVZip (os i) r rs = r :: rs
1≤th-insertVZip (o' i) r nil = r :: nil
1≤th-insertVZip (o' i) r (r' :: rs) = r' :: 1≤th-insertVZip i r rs

1≤th-removeVZip : forall {a b r A B R n xs ys} ->
                  (i : 1 ≤th succ n) ->
                  VZip {a} {b} {r} {A} {B} R {succ n} xs ys ->
                  VZip R (1≤th-removeVec i xs) (1≤th-removeVec i ys)
1≤th-removeVZip (os i) (r :: rs) = rs
1≤th-removeVZip {n = zero} (o' ()) (r :: rs)
1≤th-removeVZip {n = succ n} (o' i) (r :: rs) = r :: 1≤th-removeVZip i rs

1≤th-removeVec-insertVec :
  forall {a A m} i x (xs : Vec {a} A m) ->
  VZip _==_ (1≤th-removeVec i (1≤th-insertVec i x xs)) xs
1≤th-removeVec-insertVec (os i) x xs = ==VZip refl
1≤th-removeVec-insertVec (o' ()) x nil
1≤th-removeVec-insertVec (o' i) x (x' :: xs) = refl :: 1≤th-removeVec-insertVec i x xs

1≤th-insertVec-replicateVec :
  forall {a A n} (i : 1 ≤th succ n) x ->
  VZip _==_ (1≤th-insertVec i x (replicateVec {a} {A} n x)) (replicateVec (succ n) x)
1≤th-insertVec-replicateVec (os i) x = ==VZip refl
1≤th-insertVec-replicateVec {n = zero} (o' i) x = ==VZip refl
1≤th-insertVec-replicateVec {n = succ n} (o' i) x =
  refl :: 1≤th-insertVec-replicateVec i x

replicateVec-+V :
  forall {a A} l m x ->
  VZip _==_ (replicateVec {a} {A} (l +N m) x) (replicateVec l x +V replicateVec m x)
replicateVec-+V zero m x = ==VZip refl
replicateVec-+V (succ l) m x = refl :: replicateVec-+V l m x

is-1≤th-insertVec :
  forall {a A n} i xs ->
  Sg (Vec {a} A n) \ xs' -> VZip _==_ xs (1≤th-insertVec i (1≤th-index i xs) xs')
is-1≤th-insertVec (os i) (x :: xs) = xs , ==VZip refl
is-1≤th-insertVec {n = zero} (o' ()) (x :: xs)
is-1≤th-insertVec {n = succ n} (o' i) (x :: xs) =
  mapSg (x ::_) (refl ::_) (is-1≤th-insertVec i xs)

--punchOutNVZip : forall {a b r A B R m n xs ys}
--                VZip R xs ys -> VZip R (punchOutN m)

module RelProp where
  data RelProp (n : Nat) : Set where
    impl : RelProp (succ n) -> RelProp n
    expl : RelProp (succ n) -> RelProp n
    hyp  : (x y : 1 ≤th n) -> RelProp n -> RelProp n
    conc : (x y : 1 ≤th n) -> RelProp n

  ⟦_⟧RPT : forall {a} -> Nat -> Set a -> (r : Level) -> Set (lsuc (a ⊔ r))
  ⟦ zero ⟧RPT A r = Set _
  ⟦ succ n ⟧RPT A r = A -> ⟦ n ⟧RPT A r

  ⟦_⟧RP : forall {a r n} -> RelProp n -> {A : Set a} -> (A -> A -> Set r) -> ⟦ n ⟧RPT A r
  ⟦_⟧RP {r = r} (impl rp) {A} R = go (⟦ rp ⟧RP R)
    where
    go : forall {n} -> (A -> ⟦ n ⟧RPT A r) -> ⟦ n ⟧RPT A r
    go {zero} f = {z : A} -> f z
    go {succ n} f = \ z -> go {n} (f z)
  ⟦_⟧RP {r = r} (expl rp) {A} R = go (⟦ rp ⟧RP R)
    where
    go : forall {n} -> (A -> ⟦ n ⟧RPT A r) -> ⟦ n ⟧RPT A r
    go {zero} f = (z : A) -> f z
    go {succ n} f = \ z -> go {n} (f z)
  ⟦_⟧RP {a = a} {r} (hyp x y rp) {A} R = go x y (⟦ rp ⟧RP R)
    where
    padBoth : forall {n} -> Set (a ⊔ r) -> ⟦ n ⟧RPT A r -> ⟦ n ⟧RPT A r
    padBoth {zero} T t = T -> t
    padBoth {succ n} T t = \ z -> padBoth T (t z)

    go1 : forall {n} -> 1 ≤th n -> (A -> Set (a ⊔ r)) -> ⟦ n ⟧RPT A r -> ⟦ n ⟧RPT A r
    go1 (os x) P t = \ z -> padBoth (P z) (t z)
    go1 (o' x) P t = \ z -> go1 x P (t z)

    go : forall {n} -> (x y : 1 ≤th n) -> ⟦ n ⟧RPT A r -> ⟦ n ⟧RPT A r
    go (os x) (os y) t = \ z -> padBoth (Lift {r} {a} (R z z)) (t z)
    go (os x) (o' y) t = \ z -> go1 y (\ z' -> Lift {r} {a} (R z z')) (t z)
    go (o' x) (os y) t = \ z -> go1 x (\ z' -> Lift {r} {a} (R z' z)) (t z)
    go (o' x) (o' y) t = \ z -> go x y (t z)
  ⟦_⟧RP {a = a} {r} {n} (conc x y) {A} R = go x y
    where
    padBoth : forall {n} -> Set (a ⊔ r) -> ⟦ n ⟧RPT A r
    padBoth {n = zero} T = T
    padBoth {n = succ n} T = \ _ -> padBoth T

    go1 : forall {n} -> 1 ≤th n -> (A -> Set (a ⊔ r)) -> ⟦ n ⟧RPT A r
    go1 (os x) P = \ z -> padBoth (P z)
    go1 (o' x) P = \ _ -> go1 x P

    go : forall {n} -> (x y : 1 ≤th n) -> ⟦ n ⟧RPT A r
    go (os x) (os y) = \ z -> padBoth (Lift {r} {a} (R z z))
    go (os x) (o' y) = \ z -> go1 y (\ z' -> Lift {r} {a} (R z z'))
    go (o' x) (os y) = \ z -> go1 x (\ z' -> Lift {r} {a} (R z' z))
    go (o' x) (o' y) = \ _ -> go x y

  reflSyntax : RelProp 0
  reflSyntax = expl (conc (os oz) (os oz))

  symSyntax : RelProp 0
  symSyntax = impl (impl (hyp (os (o' oz)) (o' (os oz)) (conc (o' (os oz)) (os (o' oz)))))

  transSyntax : RelProp 0
  transSyntax = impl (impl (impl (hyp (os (o' (o' oz))) (o' (os (o' oz)))
                                      (hyp (o' (os (o' oz))) (o' (o' (os oz)))
                                           (conc (os (o' (o' oz))) (o' (o' (os oz))))))))

{-+}
VZipLift : forall {t a b r} (T : (A : Set a) (B : Set b) (R : A -> B -> Set (a ⊔ b ⊔ r)) -> Set t) ->
           {A : Set a} {B : Set b} (R : A -> B -> Set (a ⊔ b ⊔ r)) ->
           T A B R -> forall {n} -> T (Vec A n) (Vec B n) (VZip R)
VZipLift T R t {zero} = {!!}
VZipLift T R t {succ n} = {!!}
{+-}
-- T : forall A (R : A -> A -> Set) -> Set
-- T A R = (x : A) -> R x x) A R
-- refl : (x : C) -> x ≈ x  =  (\ A R -> (x : A) -> R x x) A R
-- vecrefl : {n} (x : Vec C n) -> VZip _≈_ x x  =  forall {n} -> T (Vec C n) (VZip R)

data Maybe {a} (A : Set a) : Set a where
  just : A -> Maybe A
  nothing : Maybe A

mapMaybe : forall {a b} {A : Set a} {B : Set b} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe f (just x) = just (f x)
mapMaybe f nothing = nothing

infixr 4 _>>=_ _*M_
_>>=_ : forall {a b} {A : Set a} {B : Set b} -> Maybe A -> (A -> Maybe B) -> Maybe B
just a >>= amb = amb a
nothing >>= amb = nothing

Dec->Maybe : forall {a A} -> Dec {a} A -> Maybe A
Dec->Maybe (yes p) = just p
Dec->Maybe (no np) = nothing

_*M_ : forall {a b A B} -> Maybe {a} A -> Maybe {b} B -> Maybe (A * B)
just x *M just y = just (x , y)
just x *M nothing = nothing
nothing *M mb = nothing

IfJust : forall {a p A} -> Maybe {a} A -> (A -> Set p) -> Set p
IfJust (just x) P = P x
IfJust nothing P = Lift One

data IfJust' {a p A} (P : A -> Set p) : Maybe {a} A -> Set p where
  ifJust : forall {x} -> P x -> IfJust' P (just x)

IfJust-mapMaybe : forall {a b p A} {B : Set b}
                  (P : B -> Set p) (f : A -> B) (ma : Maybe {a} A) ->
                  IfJust ma (P o f) -> IfJust (mapMaybe f ma) P
IfJust-mapMaybe P f (just a) x = x
IfJust-mapMaybe P f nothing x = x

nothing/=just : forall {a A x} -> nothing {a} {A} == just x -> Zero
nothing/=just ()
