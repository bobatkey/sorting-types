open import Setoid as Setoid'
open import Structure

module Bidirectional {c l'} (C : Set c) (MSS : MeetSemilatticeSemiring (==-Setoid C) l') where

open MeetSemilatticeSemiring MSS

open import Common
  hiding (LTy; KEY; LIST; _<**>_; _&_; _-o_; Ctx)
  renaming (_*_ to _×_; _*?_ to _×?_)
open import FunctionProperties
--open import Quantified S MSS using (QTy)
open Structure (==-Setoid C)

infixr 30 _~>_ _<**>_ _&_ _||_
data QTy : Set c where
  BASE                 : QTy
  _<**>_ _&_ _||_ _~>_ : QTy -> QTy -> QTy
  BANG                 : C -> QTy -> QTy

Ctx : Nat -> Set c
Ctx = Vec QTy

QCtx : Nat -> Set c
QCtx = Vec C

_≈Ctx_ : forall {n} (D D' : Ctx n) -> Set c
_≈Ctx_ = VZip _==_

≈Ctx-refl : forall {n} (D : Ctx n) -> D ≈Ctx D
≈Ctx-refl nil = nil
≈Ctx-refl (S :: D) = refl :: ≈Ctx-refl D

≈Ctx-sym : forall {n} {D D' : Ctx n} -> D ≈Ctx D' -> D' ≈Ctx D
≈Ctx-sym nil = nil
≈Ctx-sym (r :: eq) = sym r :: ≈Ctx-sym eq

≈Ctx-trans : forall {n} {D D' D'' : Ctx n} -> D ≈Ctx D' -> D' ≈Ctx D'' -> D ≈Ctx D''
≈Ctx-trans nil nil = nil
≈Ctx-trans (r :: eq) (r' :: eq') = trans r r' :: ≈Ctx-trans eq eq'

constQCtx : forall n -> C -> QCtx n
constQCtx zero rho = nil
constQCtx (succ n) rho = rho :: constQCtx n rho

varQCtx : forall {n} -> 1 ≤th n -> C -> QCtx n
varQCtx (os th) rho = rho :: constQCtx _ rho
varQCtx (o' th) rho = e0 :: varQCtx th rho

infix 4 _≈G_ _≤G_

_≈G_ : forall {n} (G' G : QCtx n) -> Set _
_≈G_ = VZip _==_

_≤G_ : forall {n} (G' G : QCtx n) -> Set _
_≤G_ = VZip _≤_

infixl 5 _+G_
infixl 6 _*G_

_+G_ : forall {n} (G0 G1 : QCtx n) -> QCtx n
_+G_ = vzip _+_

_*G_ : forall {n} -> C -> QCtx n -> QCtx n
_*G_ rho = vmap (rho *_)

data Dir : Set where
  syn chk : Dir

data Term (n : Nat) : Dir -> Set c where
  var : 1 ≤th n -> Term n syn
  app : (e : Term n syn) (s : Term n chk) -> Term n syn
  proj0 proj1 : (e : Term n syn) -> Term n syn
  the : (T : QTy) (s : Term n chk) -> Term n syn

  lam : (s : Term (succ n) chk) -> Term n chk
  ten : (s0 s1 : Term n chk) -> Term n chk
  pm : (e : Term n syn) (s : Term (succ (succ n)) chk) -> Term n chk
  wth : (s0 s1 : Term n chk) -> Term n chk
  inj0 inj1 : (s : Term n chk) -> Term n chk
  case : (e : Term n syn) (s0 s1 : Term (succ n) chk) -> Term n chk
  bang : (s : Term n chk) -> Term n chk
  [_] : (e : Term n syn) -> Term n chk

infix 3 _|-_∈_ _|-_∋_ _|-[_]_∈ _|-[_]∋_

data _|-_∈_ {n} (D : Ctx n) : Term n syn -> QTy -> Set c
data _|-_∋_ {n} (D : Ctx n) : QTy -> Term n chk -> Set c

data _|-_∈_ {n} (D : Ctx n) where
  var : forall {th}
        ->
        D |- var th ∈ (1≤th-index th D)
  app : forall {e s S T}
        (et : D |- e ∈ S ~> T) (st : D |- S ∋ s)
        ->
        D |- app e s ∈ T
  proj0 : forall {e S T}
          (et : D |- e ∈ S & T)
          ->
          D |- proj0 e ∈ S
  proj1 : forall {e S T}
          (et : D |- e ∈ S & T)
          ->
          D |- proj1 e ∈ T
  the : forall {S s}
        (st : D |- S ∋ s)
        ->
        D |- the S s ∈ S

data _|-_∋_ {n} (D : Ctx n) where
  lam : forall {s S T}
        (st : S :: D |- T ∋ s)
        ->
        D |- S ~> T ∋ lam s
  ten : forall {s0 s1 S0 S1}
        (s0t : D |- S0 ∋ s0) (s1t : D |- S1 ∋ s1)
        ->
        D |- S0 <**> S1 ∋ ten s0 s1
  pm : forall {e s S T U}
       (et : D |- e ∈ S <**> T) (st : T :: S :: D |- U ∋ s)
       ->
       D |- U ∋ pm e s
  wth : forall {s0 s1 S0 S1}
        (s0t : D |- S0 ∋ s0) (s1t : D |- S1 ∋ s1)
        ->
        D |- S0 & S1 ∋ wth s0 s1
  inj0 : forall {s S T}
         (st : D |- S ∋ s)
         ->
         D |- S || T ∋ inj0 s
  inj1 : forall {s S T}
         (st : D |- T ∋ s)
         ->
         D |- S || T ∋ inj1 s
  case : forall {e s0 s1 S T U}
         (et : D |- e ∈ S || T) (s0t : S :: D |- U ∋ s0) (s1t : T :: D |- U ∋ s1)
         ->
         D |- U ∋ case e s0 s1
  bang : forall {s T rho}
         (st : D |- T ∋ s)
         ->
         D |- BANG rho T ∋ bang s
  [_] : forall {e T}
        (et : D |- e ∈ T)
        ->
        D |- T ∋ [ e ]

sg->rho : Two -> C
sg->rho tt = e1
sg->rho ff = e0

data _|-[_]_∈ {n D} (G : Vec C n) (sg : Two)
              : forall {e S} -> D |- e ∈ S -> Set (l' ⊔ c)
data _|-[_]∋_ {n D} (G : Vec C n) (sg : Two)
              : forall {s S} -> D |- S ∋ s -> Set (l' ⊔ c)

data _|-[_]_∈ {n D} (G : Vec C n) (sg : Two) where
  var : forall {th}
        (sub : G ≤G varQCtx th (sg->rho sg))
        ->
        G |-[ sg ] var {th = th} ∈
  app : forall {e s S T Ge Gs et st}
        (split : G ≈G Ge +G Gs)
        (er : G |-[ sg ] et ∈) (sr : G |-[ sg ]∋ st)
        ->
        G |-[ sg ] app {e = e} {s} {S} {T} et st ∈
  proj0 : forall {e S T et}
          (er : G |-[ sg ] et ∈)
          ->
          G |-[ sg ] proj0 {e = e} {S} {T} et ∈
  proj1 : forall {e S T et}
          (er : G |-[ sg ] et ∈)
          ->
          G |-[ sg ] proj1 {e = e} {S} {T} et ∈
  the : forall {S s st}
        (sr : G |-[ sg ]∋ st)
        ->
        G |-[ sg ] the {S = S} {s} st ∈

data _|-[_]∋_ {n D} (G : Vec C n) (sg : Two) where
  lam : forall {s S T st}
        (sr : sg->rho sg :: G |-[ sg ]∋ st)
        ->
        G |-[ sg ]∋ lam {s = s} {S} {T} st
  ten : forall {s0 s1 S T s0t s1t Gs0 Gs1}
        (split : G ≈G Gs0 +G Gs1)
        (s0r : Gs0 |-[ sg ]∋ s0t) (s1r : Gs1 |-[ sg ]∋ s1t)
        ->
        G |-[ sg ]∋ ten {s0 = s0} {s1} {S} {T} s0t s1t
  pm : forall {e s S T U et st}
       (er : G |-[ sg ] et ∈) (sr : sg->rho sg :: sg->rho sg :: G |-[ sg ]∋ st)
       ->
       G |-[ sg ]∋ pm {e = e} {s} {S} {T} {U} et st
  wth : forall {s0 s1 S T s0t s1t}
        (s0r : G |-[ sg ]∋ s0t) (s1r : G |-[ sg ]∋ s1t)
        ->
        G |-[ sg ]∋ wth {s0 = s0} {s1} {S} {T} s0t s1t
  inj0 : forall {s S T st}
         (sr : G |-[ sg ]∋ st)
         ->
         G |-[ sg ]∋ inj0 {s = s} {S} {T} st
  inj1 : forall {s S T st}
         (sr : G |-[ sg ]∋ st)
         ->
         G |-[ sg ]∋ inj1 {s = s} {S} {T} st
  case : forall {e s0 s1 S T U et s0t s1t}
         (er : G |-[ sg ] et ∈)
         (s0r : sg->rho sg :: G |-[ sg ]∋ s0t) (s1r : sg->rho sg :: G |-[ sg ]∋ s0t)
         ->
         G |-[ sg ]∋ case {e = e} {s0} {s1} {S} {T} {U} et s0t s1t
  bang : forall {s T rho st Gs}
         (split : G ≈G rho *G Gs)
         (sr : Gs |-[ sg ]∋ st)
         ->
         G |-[ sg ]∋ bang {s = s} {T} {rho} st
  [_] : forall {e T et}
        (er : G |-[ sg ] et ∈)
        ->
        G |-[ sg ]∋ [_] {e = e} {T} et

1≤th-indexCong : forall {n} {D D' : Ctx n} th -> D ≈Ctx D' -> 1≤th-index th D == 1≤th-index th D'
1≤th-indexCong (os th) (r :: eq) = r
1≤th-indexCong (o' th) (r :: eq) = 1≤th-indexCong th eq

{-+}
typingCong : forall {n D D' a S S'} {x : Term n a} -> D ≈Ctx D' -> S ==QTy S' -> D |- x ∋∈ S -> D' |- x ∋∈ S'
typingCong Deq Seq (var {th = th} eq) =
  var (==QTy-trans (==QTy-sym (1≤th-indexCong th Deq)) (==QTy-trans eq Seq))
typingCong Deq Seq (app et st) =
  app (typingCong Deq (==QTy-refl _ ~> Seq) et) (typingCong Deq (==QTy-refl _) st)
typingCong Deq Seq (pm et st) =
  pm (typingCong (==QTy-refl _ :: ==QTy-refl _ :: Deq) Seq et)
     (typingCong Deq (==QTy-refl _ <**> ==QTy-refl _) st)
typingCong Deq Seq (proj0 st) =
  proj0 (typingCong Deq (Seq & ==QTy-refl _) st)
typingCong Deq Seq (proj1 st) =
  proj1 (typingCong Deq (==QTy-refl _ & Seq) st)
typingCong Deq Seq (case e0t e1t st) =
  case (typingCong (==QTy-refl _ :: Deq) Seq e0t)
       (typingCong (==QTy-refl _ :: Deq) Seq e1t)
       (typingCong Deq (==QTy-refl _) st)
typingCong Deq Seq (the eq st) =
  the (==QTy-trans eq Seq) (typingCong Deq Seq st)

typingCong Deq (Seq ~> Teq) (lam st) =
  lam (typingCong (Seq :: Deq) Teq st)
typingCong Deq (Seq <**> Teq) (ten s0t s1t) =
  ten (typingCong Deq Seq s0t) (typingCong Deq Teq s1t)
typingCong Deq (Seq & Teq) (wth s0t s1t) =
  wth (typingCong Deq Seq s0t) (typingCong Deq Teq s1t)
typingCong Deq (Seq || Teq) (inj0 st) =
  inj0 (typingCong Deq Seq st)
typingCong Deq (Seq || Teq) (inj1 st) =
  inj1 (typingCong Deq Teq st)
typingCong Deq (BANG rhoeq Seq) (bang st) =
  bang (typingCong Deq Seq st)
typingCong Deq Seq [ et ] =
  [ typingCong Deq Seq et ]
{+-}

module DecEq (_==?_ : (rho rho' : C) -> Dec (rho == rho')) where
  _==QTy?_ : (S S' : QTy) -> Dec (S == S')
  BASE ==QTy? BASE = yes refl
  BASE ==QTy? (S' <**> T') = no \ ()
  BASE ==QTy? (S' & T') = no \ ()
  BASE ==QTy? (S' || T') = no \ ()
  BASE ==QTy? (S' ~> T') = no \ ()
  BASE ==QTy? BANG rho' S' = no \ ()
  (S <**> T) ==QTy? BASE = no \ ()
  (S <**> T) ==QTy? (S' <**> T') =
    mapDec (\ { (refl , refl) -> refl })
           (\ { refl -> (refl , refl) })
           ((S ==QTy? S') ×? (T ==QTy? T'))
  (S <**> T) ==QTy? (S' & T') = no \ ()
  (S <**> T) ==QTy? (S' || T') = no \ ()
  (S <**> T) ==QTy? (S' ~> T') = no \ ()
  (S <**> T) ==QTy? BANG rho' S' = no \ ()
  (S & T) ==QTy? BASE = no \ ()
  (S & T) ==QTy? (S' <**> T') = no \ ()
  (S & T) ==QTy? (S' & T') =
    mapDec (\ { (refl , refl) -> refl })
           (\ { refl -> (refl , refl) })
           ((S ==QTy? S') ×? (T ==QTy? T'))
  (S & T) ==QTy? (S' || T') = no \ ()
  (S & T) ==QTy? (S' ~> T') = no \ ()
  (S & T) ==QTy? BANG rho' S' = no \ ()
  (S || T) ==QTy? BASE = no \ ()
  (S || T) ==QTy? (S' <**> T') = no \ ()
  (S || T) ==QTy? (S' & T') = no \ ()
  (S || T) ==QTy? (S' || T') =
    mapDec (\ { (refl , refl) -> refl })
           (\ { refl -> (refl , refl) })
           ((S ==QTy? S') ×? (T ==QTy? T'))
  (S || T) ==QTy? (S' ~> T') = no \ ()
  (S || T) ==QTy? BANG rho' S' = no \ ()
  (S ~> T) ==QTy? BASE = no \ ()
  (S ~> T) ==QTy? (S' <**> T') = no \ ()
  (S ~> T) ==QTy? (S' & T') = no \ ()
  (S ~> T) ==QTy? (S' || T') = no \ ()
  (S ~> T) ==QTy? (S' ~> T') =
    mapDec (\ { (refl , refl) -> refl })
           (\ { refl -> (refl , refl) })
           ((S ==QTy? S') ×? (T ==QTy? T'))
  (S ~> T) ==QTy? BANG rho' S' = no \ ()
  BANG rho S ==QTy? BASE = no \ ()
  BANG rho S ==QTy? (S' <**> T') = no \ ()
  BANG rho S ==QTy? (S' & T') = no \ ()
  BANG rho S ==QTy? (S' || T') = no \ ()
  BANG rho S ==QTy? (S' ~> T') = no \ ()
  BANG rho S ==QTy? BANG rho' S' =
    mapDec (\ { (refl , refl) -> refl })
           (\ { refl -> (refl , refl) })
           ((rho ==? rho') ×? (S ==QTy? S'))

  {-+}
  typesUnique : forall {n a} {D : Ctx n} {x : Term n a} {S S' : QTy} ->
                D |- x ∋∈ S -> D |- x ∋∈ S' -> S == S'
  typesUnique var var = refl
  typesUnique (app et st) (app et' st') with typesUnique et et'
  ... | refl = refl
  typesUnique (pm et st) (pm et' st') with typesUnique st st'
  ... | refl = typesUnique et et'
  typesUnique (proj0 st) (proj0 st') with typesUnique st st'
  ... | refl = refl
  typesUnique (proj1 st) (proj1 st') with typesUnique st st'
  ... | refl = refl
  typesUnique (case e0t e1t st) (case e0t' e1t' st') with typesUnique st st'
  ... | refl = typesUnique e0t e0t'
  typesUnique (the st) (the st') = refl
  typesUnique (lam st) (lam st') = {!!}
  typesUnique (ten s0t s1t) (ten s0t' s1t') = {!!}
  typesUnique (wth s0t s1t) (wth s0t' s1t') = {!!}
  typesUnique (inj0 st) (inj0 st') = {!!}
  typesUnique (inj1 st) (inj1 st') = {!!}
  typesUnique (bang st) (bang st') = {!!}
  typesUnique [ et ] [ et' ] = {!!}
  {+-}

  Is<**>? : forall S -> Dec (Sg _ \ S0 -> Sg _ \ S1 -> S0 <**> S1 == S)
  Is<**>? BASE = no \ { (_ , _ , ()) }
  Is<**>? (S0 <**> S1) = yes (S0 , S1 , refl)
  Is<**>? (S0 & S1) = no \ { (_ , _ , ()) }
  Is<**>? (S0 || S1) = no \ { (_ , _ , ()) }
  Is<**>? (S0 ~> S1) = no \ { (_ , _ , ()) }
  Is<**>? (BANG x S1) = no \ { (_ , _ , ()) }

  Is&? : forall S -> Dec (Sg _ \ S0 -> Sg _ \ S1 -> S0 & S1 == S)
  Is&? BASE = no \ { (_ , _ , ()) }
  Is&? (S0 <**> S1) = no \ { (_ , _ , ()) }
  Is&? (S0 & S1) = yes (S0 , S1 , refl)
  Is&? (S0 || S1) = no \ { (_ , _ , ()) }
  Is&? (S0 ~> S1) = no \ { (_ , _ , ()) }
  Is&? (BANG x S) = no \ { (_ , _ , ()) }

  Is||? : forall S -> Dec (Sg _ \ S0 -> Sg _ \ S1 -> S0 || S1 == S)
  Is||? BASE = no \ { (_ , _ , ()) }
  Is||? (S0 <**> S1) = no \ { (_ , _ , ()) }
  Is||? (S0 & S1) = no \ { (_ , _ , ()) }
  Is||? (S0 || S1) = yes (S0 , S1 , refl)
  Is||? (S0 ~> S1) = no \ { (_ , _ , ()) }
  Is||? (BANG x S) = no \ { (_ , _ , ()) }

  Is~>? : forall S -> Dec (Sg _ \ S0 -> Sg _ \ S1 -> S0 ~> S1 == S)
  Is~>? BASE = no \ { (_ , _ , ()) }
  Is~>? (S0 <**> S1) = no \ { (_ , _ , ()) }
  Is~>? (S0 & S1) = no \ { (_ , _ , ()) }
  Is~>? (S0 || S1) = no \ { (_ , _ , ()) }
  Is~>? (S0 ~> S1) = yes (S0 , S1 , refl)
  Is~>? (BANG x S) = no \ { (_ , _ , ()) }

  IsBANG? : forall S -> Dec (Sg _ \ rho -> Sg _ \ T -> BANG rho T == S)
  IsBANG? BASE = no \ { (_ , _ , ()) }
  IsBANG? (S0 <**> S1) = no \ { (_ , _ , ()) }
  IsBANG? (S0 & S1) = no \ { (_ , _ , ()) }
  IsBANG? (S0 || S1) = no \ { (_ , _ , ()) }
  IsBANG? (S0 ~> S1) = no \ { (_ , _ , ()) }
  IsBANG? (BANG rho S) = yes (rho , S , refl)

  synthUnique : forall {n} {D : Ctx n} {e : Term n syn} {S S' : QTy} ->
                D |- e ∈ S -> D |- e ∈ S' -> S' == S
  synthUnique var var = refl
  synthUnique (app et st) (app et' st') with synthUnique et et'
  ... | refl = refl
  synthUnique (proj0 et) (proj0 et') with synthUnique et et'
  ... | refl = refl
  synthUnique (proj1 et) (proj1 et') with synthUnique et et'
  ... | refl = refl
  synthUnique (the st) (the st') = refl

  synthType : forall {n} (D : Ctx n) (e : Term n syn) ->
              Dec (Sg _ \ S -> D |- e ∈ S)
  checkType : forall {n} (D : Ctx n) (S : QTy) (s : Term n chk) ->
              Dec (D |- S ∋ s)

  synthType D (var th) = yes (1≤th-index th D , var)
  synthType D (app e s) with synthType D e
  ... | no np = no (np o \ { (_ , app et st) -> _ , et })
  ... | yes (ST , et) with Is~>? ST
  ...   | no np = no \ { (_ , app et' st') → np (_ , _ , synthUnique et et') }
  ...   | yes (S0 , S1 , refl) =
    mapDec (\ st -> S1 , app et st) inv (checkType D S0 s)
    where
    inv : (Sg _ \ T' -> D |- app e s ∈ T') -> D |- S0 ∋ s
    inv (T' , app et' st') with synthUnique et et'
    ... | refl = st'
  synthType D (proj0 e) with synthType D e
  ... | no np = no (np o \ { (_ , proj0 et) -> _ , et })
  ... | yes (S , et) with Is&? S
  ...   | no np = no (np o \ { (_ , proj0 et') -> _ , _ , synthUnique et et' })
  ...   | yes (S0 , S1 , refl) = yes (S0 , proj0 et)
  synthType D (proj1 e) =
    -- testing out monadic-like syntax:
    -- test >>=[ if-fail ] \ success-evidence ->
    -- rest...
    synthType D e >>=[ (\ { (_ , proj1 et) -> _ , et }) ] \ { (S , et) ->
    Is&? S >>=[ (\ { (_ , proj1 et') -> _ , _ , synthUnique et et' }) ] \ { (S0 , S1 , refl) ->
    yes (S1 , proj1 et) } }
  synthType D (the T s) = mapDec (\ st -> T , the st) (\ { (_ , the st) -> st }) (checkType D T s)

  checkType D S (lam s) with Is~>? S
  ... | no np = no (np o \ { (lam st) -> _ , _ , refl })
  ... | yes (S0 , S1 , refl) =
    mapDec lam (\ { (lam st) -> st }) (checkType (S0 :: D) S1 s)
  checkType D ST (ten s0 s1) with Is<**>? ST
  ... | no np = no (np o \ { (ten s0t s1t) -> _ , _ , refl })
  ... | yes (S , T , refl) =
    mapDec (uncurry ten) (\ { (ten s0t s1t) -> s0t , s1t }) (checkType D S s0 ×? checkType D T s1)
  checkType D U (pm e s) with synthType D e
  ... | no np = no (np o \ { (pm et' st') -> _ , et' })
  ... | yes (ST , et) with Is<**>? ST
  ...   | no np =
    no (np o \ { (pm et' st') -> _ , _ , synthUnique et et' })
  ...   | yes (S , T , refl) =
    mapDec (pm et) inv (checkType (T :: S :: D) U s)
    where
    inv : D |- U ∋ pm e s -> T :: S :: D |- U ∋ s
    inv (pm et' st') with synthUnique et et'
    ... | refl = st'
  checkType D S (wth s0 s1) with Is&? S
  ... | no np = no \ { (wth s0t s1t) -> np (_ , _ , refl) }
  ... | yes (S0 , S1 , refl) =
    mapDec (\ { (s0t , s1t) -> wth s0t s1t })
           (\ { (wth s0t s1t) -> s0t , s1t })
           (checkType D S0 s0 ×? checkType D S1 s1)
  checkType D S (inj0 s) with Is||? S
  ... | no np = no (np o \ { (inj0 st) -> _ , _ , refl })
  ... | yes (S0 , S1 , refl) =
    mapDec inj0 (\ { (inj0 st) -> st }) (checkType D S0 s)
  checkType D ST (inj1 s) =
    Is||? ST >>=[ (\ { (inj1 st) -> _ , _ , refl }) ] \ { (S , T , refl) ->
    checkType D T s >>=[ (\ { (inj1 st) -> st }) ]
    yes o inj1 }
  checkType D U (case e s0 s1) with synthType D e
  ... | no np = no (np o \ { (case et s0t s1t) -> _ , et })
  ... | yes (ST , et) with Is||? ST
  ...   | no np = no (np o \ { (case et' s0t' s1t') -> _ , _ , synthUnique et et' })
  ...   | yes (S , T , refl) =
    mapDec (uncurry (case et)) inv (checkType (S :: D) U s0 ×? checkType (T :: D) U s1)
    where
    inv : D |- U ∋ case e s0 s1 -> (S :: D |- U ∋ s0) × (T :: D |- U ∋ s1)
    inv (case et' s0t' s1t') with synthUnique et et'
    ... | refl = s0t' , s1t'
  checkType D S (bang s) with IsBANG? S
  ... | no np = no (np o \ { (bang st) -> _ , _ , refl })
  ... | yes (rho , T , refl) = mapDec bang (\ { (bang st) -> st }) (checkType D T s)
  checkType D S [ e ] with synthType D e
  ... | no np = no (np o \ { [ et ] -> S , et })
  ... | yes (S' , et) = mapDec (\ { refl -> [ et ] }) (\ { [ et' ] → synthUnique et et' }) (S ==QTy? S')
