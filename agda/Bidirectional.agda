open import Setoid as Setoid'
open import Structure

module Bidirectional {c l l'} (S : Setoid c l) (MSS : MeetSemilatticeSemiring S l') where

open Setoid S
open MeetSemilatticeSemiring MSS

open import Common
  hiding (LTy; KEY; LIST; _<**>_; _&_; _-o_; Ctx)
  renaming (_*_ to _×_; _*?_ to _×?_; refl to ==-refl; sym to ==-sym; trans to ==-trans)
open import FunctionProperties
--open import Quantified S MSS using (QTy)
open Structure S

infixr 30 _~>_ _<**>_ _&_ _||_
data QTy : Set c where
  BASE                 : QTy
  _<**>_ _&_ _||_ _~>_ : QTy -> QTy -> QTy
  BANG                 : C -> QTy -> QTy

data _≈QTy_ : (S T : QTy) -> Set (l ⊔ c) where
  BASE : BASE ≈QTy BASE
  _<**>_ : forall {S T S' T'} -> S ≈QTy S' -> T ≈QTy T' -> S <**> T ≈QTy S' <**> T'
  _&_ : forall {S T S' T'} -> S ≈QTy S' -> T ≈QTy T' -> S & T ≈QTy S' & T'
  _||_ : forall {S T S' T'} -> S ≈QTy S' -> T ≈QTy T' -> S || T ≈QTy S' || T'
  _~>_ : forall {S T S' T'} -> S ≈QTy S' -> T ≈QTy T' -> S ~> T ≈QTy S' ~> T'
  BANG : forall {rho rho' S S'} -> rho ≈ rho' -> S ≈QTy S' -> BANG rho S ≈QTy BANG rho' S'

≈QTy-refl : forall S -> S ≈QTy S
≈QTy-refl BASE = BASE
≈QTy-refl (S <**> T) = ≈QTy-refl S <**> ≈QTy-refl T
≈QTy-refl (S & T) = ≈QTy-refl S & ≈QTy-refl T
≈QTy-refl (S || T) = ≈QTy-refl S || ≈QTy-refl T
≈QTy-refl (S ~> T) = ≈QTy-refl S ~> ≈QTy-refl T
≈QTy-refl (BANG rho S) = BANG refl (≈QTy-refl S)

≈QTy-trans : forall {S T U} -> S ≈QTy T -> T ≈QTy U -> S ≈QTy U
≈QTy-trans BASE BASE = BASE
≈QTy-trans (ST0 <**> ST1) (TU0 <**> TU1) = ≈QTy-trans ST0 TU0 <**> ≈QTy-trans ST1 TU1
≈QTy-trans (ST0 & ST1) (TU0 & TU1) = ≈QTy-trans ST0 TU0 & ≈QTy-trans ST1 TU1
≈QTy-trans (ST0 || ST1) (TU0 || TU1) = ≈QTy-trans ST0 TU0 || ≈QTy-trans ST1 TU1
≈QTy-trans (ST0 ~> ST1) (TU0 ~> TU1) = ≈QTy-trans ST0 TU0 ~> ≈QTy-trans ST1 TU1
≈QTy-trans (BANG rho ST) (BANG rho' TU) = BANG (trans rho rho') (≈QTy-trans ST TU)

≈QTy-sym : forall {S T} -> S ≈QTy T -> T ≈QTy S
≈QTy-sym BASE = BASE
≈QTy-sym (ST0 <**> ST1) = ≈QTy-sym ST0 <**> ≈QTy-sym ST1
≈QTy-sym (ST0 & ST1) = ≈QTy-sym ST0 & ≈QTy-sym ST1
≈QTy-sym (ST0 || ST1) = ≈QTy-sym ST0 || ≈QTy-sym ST1
≈QTy-sym (ST0 ~> ST1) = ≈QTy-sym ST0 ~> ≈QTy-sym ST1
≈QTy-sym (BANG rho ST) = BANG (sym rho) (≈QTy-sym ST)

Ctx : Nat -> Set c
Ctx = Vec QTy

QCtx : Nat -> Set c
QCtx = Vec C

_≈Ctx_ : forall {n} (D D' : Ctx n) -> Set (l ⊔ c)
_≈Ctx_ = VZip _≈QTy_

≈Ctx-refl : forall {n} (D : Ctx n) -> D ≈Ctx D
≈Ctx-refl nil = nil
≈Ctx-refl (S :: D) = ≈QTy-refl S :: ≈Ctx-refl D

≈Ctx-sym : forall {n} {D D' : Ctx n} -> D ≈Ctx D' -> D' ≈Ctx D
≈Ctx-sym nil = nil
≈Ctx-sym (r :: eq) = ≈QTy-sym r :: ≈Ctx-sym eq

≈Ctx-trans : forall {n} {D D' D'' : Ctx n} -> D ≈Ctx D' -> D' ≈Ctx D'' -> D ≈Ctx D''
≈Ctx-trans nil nil = nil
≈Ctx-trans (r :: eq) (r' :: eq') = ≈QTy-trans r r' :: ≈Ctx-trans eq eq'

constQCtx : forall n -> C -> QCtx n
constQCtx zero rho = nil
constQCtx (succ n) rho = rho :: constQCtx n rho

varQCtx : forall {n} -> 1 ≤th n -> C -> QCtx n
varQCtx (os th) rho = rho :: constQCtx _ rho
varQCtx (o' th) rho = e0 :: varQCtx th rho

infix 4 _≈G_ _≤G_

_≈G_ : forall {n} (G' G : QCtx n) -> Set _
_≈G_ = VZip _≈_

_≤G_ : forall {n} (G' G : QCtx n) -> Set _
_≤G_ = VZip _≤_

infixl 5 _+G_
infixl 6 _*G_

_+G_ : forall {n} (G0 G1 : QCtx n) -> QCtx n
_+G_ = vzip _+_

_*G_ : forall {n} -> C -> QCtx n -> QCtx n
_*G_ rho = vmap (rho *_)

data Term (n : Nat) : Two -> Set c where
  var : 1 ≤th n -> Term n tt
  app : (e : Term n tt) (s : Term n ff) -> Term n tt
  pm : (e : Term (succ (succ n)) tt) (s : Term n ff) -> Term n tt
  proj0 proj1 : (s : Term n ff) -> Term n tt
  case : (e0 e1 : Term (succ n) tt) (s : Term n ff) -> Term n tt
  the : (T : QTy) (s : Term n ff) -> Term n tt

  lam : (s : Term (succ n) ff) -> Term n ff
  ten : (s0 s1 : Term n ff) -> Term n ff
  wth : (s0 s1 : Term n ff) -> Term n ff
  inj0 inj1 : (s : Term n ff) -> Term n ff
  bang : (s : Term n ff) -> Term n ff
  [_] : (e : Term n tt) -> Term n ff

infix 3 _|-_∋∈_ _|-[_]_

data _|-_∋∈_ {n} (D : Ctx n) : forall {a} -> Term n a -> QTy -> Set (l ⊔ c) where
  var : forall {th S}
        (eq : 1≤th-index th D ≈QTy S)
        ->
        D |- var th ∋∈ S
  app : forall {e s S T}
        (et : D |- e ∋∈ S ~> T) (st : D |- s ∋∈ S)
        ->
        D |- app e s ∋∈ T
  pm : forall {e s S T U}
       (et : T :: S :: D |- e ∋∈ U) (st : D |- s ∋∈ S <**> T)
       ->
       D |- pm e s ∋∈ U
  proj0 : forall {s S T}
          (st : D |- s ∋∈ S & T)
          ->
          D |- proj0 s ∋∈ S
  proj1 : forall {s S T}
          (st : D |- s ∋∈ S & T)
          ->
          D |- proj1 s ∋∈ T
  case : forall {e0 e1 s S T U}
         (e0t : S :: D |- e0 ∋∈ U) (e1t : T :: D |- e0 ∋∈ U) (st : D |- s ∋∈ S || T)
         ->
         D |- case e0 e1 s ∋∈ U
  the : forall {S T s}
        (eq : S ≈QTy T) (st : D |- s ∋∈ T)
        ->
        D |- the S s ∋∈ T

  lam : forall {s S T}
        (st : S :: D |- s ∋∈ T)
        ->
        D |- lam s ∋∈ S ~> T
  ten : forall {s0 s1 S T}
        (s0t : D |- s0 ∋∈ S) (s1t : D |- s1 ∋∈ T)
        ->
        D |- ten s0 s1 ∋∈ S <**> T
  wth : forall {s0 s1 S T}
        (s0t : D |- s0 ∋∈ S) (s1t : D |- s1 ∋∈ T)
        ->
        D |- wth s0 s1 ∋∈ S & T
  inj0 : forall {s S T}
         (st : D |- s ∋∈ S)
         ->
         D |- inj0 s ∋∈ S || T
  inj1 : forall {s S T}
         (st : D |- s ∋∈ T)
         ->
         D |- inj1 s ∋∈ S || T
  bang : forall {s T rho}
         (st : D |- s ∋∈ T)
         ->
         D |- bang s ∋∈ BANG rho T
  [_] : forall {e T}
        (et : D |- e ∋∈ T)
        ->
        D |- [ e ] ∋∈ T

_|-S_∋∈_ : forall {n} (D : Ctx n) -> forall {a} -> Term n a -> QTy -> Setoid (l ⊔ c) (l ⊔ c)
D |-S x ∋∈ T = record
  { C = D |- x ∋∈ T
  ; setoidOver = record
    { _≈_ = {!!}
    ; isSetoid = {!!}
    }
  }

sg->rho : Two -> C
sg->rho tt = e1
sg->rho ff = e0

data _|-[_]_ {n D} (G : Vec C n) (sg : Two)
             : forall {a} {x : Term n a} {S : QTy} -> D |- x ∋∈ S -> Set (l ⊔ l' ⊔ c)
             where
  var : forall {th S eq}
        (sub : G ≤G varQCtx th (sg->rho sg))
        ->
        G |-[ sg ] var {th = th} {S} eq
  app : forall {e s S T Ge Gs et st}
        (split : G ≈G Ge +G Gs)
        (er : G |-[ sg ] et) (sr : G |-[ sg ] st)
        ->
        G |-[ sg ] app {e = e} {s} {S} {T} et st
  pm : forall {e s S T U et st}
       (er : sg->rho sg :: sg->rho sg :: G |-[ sg ] et) (sr : G |-[ sg ] st)
       ->
       G |-[ sg ] pm {e = e} {s} {S} {T} {U} et st
  proj0 : forall {s S T st}
          (sr : G |-[ sg ] st)
          ->
          G |-[ sg ] proj0 {s = s} {S} {T} st
  proj1 : forall {s S T st}
          (sr : G |-[ sg ] st)
          ->
          G |-[ sg ] proj1 {s = s} {S} {T} st
  case : forall {e0 e1 s S T U e0t e1t st}
         (e0r : sg->rho sg :: G |-[ sg ] e0t) (e1r : sg->rho sg :: G |-[ sg ] e0t)
         (sr : G |-[ sg ] st)
         ->
         G |-[ sg ] case {e0 = e0} {e1} {s} {S} {T} {U} e0t e1t st
  the : forall {S T s eq st}
        (sr : G |-[ sg ] st)
        ->
        G |-[ sg ] the {S = S} {T} {s} eq st

  lam : forall {s S T st}
        (sr : sg->rho sg :: G |-[ sg ] st)
        ->
        G |-[ sg ] lam {s = s} {S} {T} st
  ten : forall {s0 s1 S T s0t s1t Gs0 Gs1}
        (split : G ≈G Gs0 +G Gs1)
        (s0r : Gs0 |-[ sg ] s0t) (s1r : Gs1 |-[ sg ] s1t)
        ->
        G |-[ sg ] ten {s0 = s0} {s1} {S} {T} s0t s1t
  wth : forall {s0 s1 S T s0t s1t}
        (s0r : G |-[ sg ] s0t) (s1r : G |-[ sg ] s1t)
        ->
        G |-[ sg ] wth {s0 = s0} {s1} {S} {T} s0t s1t
  inj0 : forall {s S T st}
         (sr : G |-[ sg ] st)
         ->
         G |-[ sg ] inj0 {s = s} {S} {T} st
  inj1 : forall {s S T st}
         (sr : G |-[ sg ] st)
         ->
         G |-[ sg ] inj1 {s = s} {S} {T} st
  bang : forall {s T rho st Gs}
         (split : G ≈G rho *G Gs)
         (sr : Gs |-[ sg ] st)
         ->
         G |-[ sg ] bang {s = s} {T} {rho} st
  [_] : forall {e T et}
        (er : G |-[ sg ] et)
        ->
        G |-[ sg ] [_] {e = e} {T} et

1≤th-indexCong : forall {n} {D D' : Ctx n} th -> D ≈Ctx D' -> 1≤th-index th D ≈QTy 1≤th-index th D'
1≤th-indexCong (os th) (r :: eq) = r
1≤th-indexCong (o' th) (r :: eq) = 1≤th-indexCong th eq

typingCong : forall {n D D' a S S'} {x : Term n a} -> D ≈Ctx D' -> S ≈QTy S' -> D |- x ∋∈ S -> D' |- x ∋∈ S'
typingCong Deq Seq (var {th = th} eq) =
  var (≈QTy-trans (≈QTy-sym (1≤th-indexCong th Deq)) (≈QTy-trans eq Seq))
typingCong Deq Seq (app et st) =
  app (typingCong Deq (≈QTy-refl _ ~> Seq) et) (typingCong Deq (≈QTy-refl _) st)
typingCong Deq Seq (pm et st) =
  pm (typingCong (≈QTy-refl _ :: ≈QTy-refl _ :: Deq) Seq et)
     (typingCong Deq (≈QTy-refl _ <**> ≈QTy-refl _) st)
typingCong Deq Seq (proj0 st) =
  proj0 (typingCong Deq (Seq & ≈QTy-refl _) st)
typingCong Deq Seq (proj1 st) =
  proj1 (typingCong Deq (≈QTy-refl _ & Seq) st)
typingCong Deq Seq (case e0t e1t st) =
  case (typingCong (≈QTy-refl _ :: Deq) Seq e0t)
       (typingCong (≈QTy-refl _ :: Deq) Seq e1t)
       (typingCong Deq (≈QTy-refl _) st)
typingCong Deq Seq (the eq st) =
  the (≈QTy-trans eq Seq) (typingCong Deq Seq st)

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

module DecEq (_≈?_ : forall rho rho' -> Dec (rho ≈ rho')) where
  _≈QTy?_ : forall S S' -> Dec (S ≈QTy S')
  BASE ≈QTy? BASE = yes BASE
  BASE ≈QTy? (S' <**> T') = no \ ()
  BASE ≈QTy? (S' & T') = no \ ()
  BASE ≈QTy? (S' || T') = no \ ()
  BASE ≈QTy? (S' ~> T') = no \ ()
  BASE ≈QTy? BANG rho' S' = no \ ()
  (S <**> T) ≈QTy? BASE = no \ ()
  (S <**> T) ≈QTy? (S' <**> T') =
    mapDec (uncurry _<**>_)
           (\ { (eqS <**> eqT) -> eqS , eqT })
           ((S ≈QTy? S') ×? (T ≈QTy? T'))
  (S <**> T) ≈QTy? (S' & T') = no \ ()
  (S <**> T) ≈QTy? (S' || T') = no \ ()
  (S <**> T) ≈QTy? (S' ~> T') = no \ ()
  (S <**> T) ≈QTy? BANG rho' S' = no \ ()
  (S & T) ≈QTy? BASE = no \ ()
  (S & T) ≈QTy? (S' <**> T') = no \ ()
  (S & T) ≈QTy? (S' & T') =
    mapDec (uncurry _&_)
           (\ { (eqS & eqT) -> eqS , eqT })
           ((S ≈QTy? S') ×? (T ≈QTy? T'))
  (S & T) ≈QTy? (S' || T') = no \ ()
  (S & T) ≈QTy? (S' ~> T') = no \ ()
  (S & T) ≈QTy? BANG rho' S' = no \ ()
  (S || T) ≈QTy? BASE = no \ ()
  (S || T) ≈QTy? (S' <**> T') = no \ ()
  (S || T) ≈QTy? (S' & T') = no \ ()
  (S || T) ≈QTy? (S' || T') =
    mapDec (uncurry _||_)
           (\ { (eqS || eqT) -> eqS , eqT })
           ((S ≈QTy? S') ×? (T ≈QTy? T'))
  (S || T) ≈QTy? (S' ~> T') = no \ ()
  (S || T) ≈QTy? BANG rho' S' = no \ ()
  (S ~> T) ≈QTy? BASE = no \ ()
  (S ~> T) ≈QTy? (S' <**> T') = no \ ()
  (S ~> T) ≈QTy? (S' & T') = no \ ()
  (S ~> T) ≈QTy? (S' || T') = no \ ()
  (S ~> T) ≈QTy? (S' ~> T') =
    mapDec (uncurry _~>_)
           (\ { (eqS ~> eqT) -> eqS , eqT })
           ((S ≈QTy? S') ×? (T ≈QTy? T'))
  (S ~> T) ≈QTy? BANG rho' S' = no \ ()
  BANG rho S ≈QTy? BASE = no \ ()
  BANG rho S ≈QTy? (S' <**> T') = no \ ()
  BANG rho S ≈QTy? (S' & T') = no \ ()
  BANG rho S ≈QTy? (S' || T') = no \ ()
  BANG rho S ≈QTy? (S' ~> T') = no \ ()
  BANG rho S ≈QTy? BANG rho' S' =
    mapDec (uncurry BANG)
           (\ { (BANG eqS eqT) -> eqS , eqT })
           ((rho ≈? rho') ×? (S ≈QTy? S'))

  inferTypes : forall {n} (D : Ctx n) (e : Term n tt) ->
               Dec (Sg _ \ S -> D |- e ∋∈ S)
  checkTypes : forall {n} (D : Ctx n) (s : Term n ff) (S : QTy) ->
               Dec (Sg _ \ S' -> S ≈QTy S' × D |- s ∋∈ S')

  inferTypes D (var x) = {!!}
  inferTypes D (app e s) = {!!}
  inferTypes D (pm e s) = {!!}
  inferTypes D (proj0 s) = {!!}
  inferTypes D (proj1 s) = {!!}
  inferTypes D (case e0 e1 s) = {!!}
  inferTypes D (the T s) = mapDec {!typingCong (≈Ctx-refl D) ?!} {!!} (checkTypes D s T)
  checkTypes D (lam s) S = {!!}
  checkTypes D (ten s0 s1) S = {!!}
  checkTypes D (wth s0 s1) S = {!!}
  checkTypes D (inj0 s) S = {!!}
  checkTypes D (inj1 s) S = {!!}
  checkTypes D (bang s) S = {!!}
  checkTypes D [ e ] S with (inferTypes D e)
  ... | no np = no (np o \ { (S' , Seq , [ et ]) -> S' , et })
  ... | yes (S' , et) = mapDec (\ Seq -> S' , Seq , [ et ]) (\ { (S'' , Seq , st) -> {!!} }) (S ≈QTy? S')
