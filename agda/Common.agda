module Common where

open import Base public

id : forall {l} {A : Set l} -> A -> A
id x = x

infixr 5 _o_
_o_ : forall {a b c} {A : Set a} {B : A -> Set b} {C : forall {a} -> B a -> Set c}
      (f : forall {a} (b : B a) -> C b) (g : forall a -> B a) a -> C (g a)
(f o g) x = f (g x)

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

infixr 5 _::_

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

infix 4 _≤th_
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

data Vec {a} (A : Set a) : Nat -> Set a where
  nil : Vec A zero
  _::_ : forall {n} (x : A) (xs : Vec A n) -> Vec A (succ n)

1≤th-index : forall {a A m} -> 1 ≤th m -> Vec {a} A m -> A
1≤th-index (os th) (x :: xs) = x
1≤th-index (o' th) (x :: xs) = 1≤th-index th xs

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

data VZip {a b r} {A : Set a} {B : Set b} (R : A -> B -> Set r)
            : forall {n} -> Vec A n -> Vec B n -> Set (a ⊔ b ⊔ r) where
  nil : VZip R nil nil
  _::_ : forall {a b n as bs} (r : R a b) (rs : VZip R {n} as bs)
         -> VZip R (a :: as) (b :: bs)

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
