module Bidirectional {c} {dummy : Set} {l'} (C : Set c) (Dummy : Set) (_≤_ : C -> C -> Set l') where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)

data List {a} (A : Set a) : Set a where
  nil : List A
  _::_ : forall (x : A) (xs : List A) -> List A

record Lift {a l} (A : Set a) : Set (a ⊔ l) where
  constructor lift
  field
    lower : A
open Lift public

record One : Set where
  constructor <>
open One public

data Maybe {a} (A : Set a) : Set a where
  just : A -> Maybe A
  nothing : Maybe A

mapMaybe : forall {a b} {A : Set a} {B : Set b} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe f (just x) = just (f x)
mapMaybe f nothing = nothing

IfJust : forall {a p A} -> Maybe {a} A -> (A -> Set p) -> Set p
IfJust (just x) P = P x
IfJust nothing P = Lift One

record Sg {a b} (A : Set a) (B : A -> Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Sg public
infixr 1 _,_

mapSg : forall {a a' b b'} {A : Set a} {A' : Set a'} {B : A -> Set b} {B' : A' -> Set b'}
        (fa : A -> A') -> (forall {a} -> B a -> B' (fa a)) -> Sg A B -> Sg A' B'
mapSg fa fb (a , b) = fa a , fb b

QCtx : Set c
QCtx = List C

data Term : Set c where
  [_] : (e : Term) -> Term

data _|-_ (G : QCtx) : Term -> Set (l' ⊔ c) where
  [_] : forall {e} (er : G |- e) -> G |- [ e ]

inferRes : (t : Term) -> Maybe (Sg _ \ G -> G |- t)
inferRes [ e ] = mapMaybe (mapSg (\ x -> x) [_]) (inferRes e)

inferResBest : (t : Term) -> IfJust (inferRes t) \ { (G , _) -> forall {G'} -> G' |- t -> One }
inferResBest [ e ] with inferRes e
... | just _ = {!inferResBest e!}
... | nothing = {!QCtx!}

-- TODO: submit report
