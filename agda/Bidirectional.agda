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

_≈D_ : forall {n} (D D' : Ctx n) -> Set c
_≈D_ = VZip _==_

≈D-refl : forall {n} (D : Ctx n) -> D ≈D D
≈D-refl nil = nil
≈D-refl (S :: D) = refl :: ≈D-refl D

≈D-sym : forall {n} {D D' : Ctx n} -> D ≈D D' -> D' ≈D D
≈D-sym nil = nil
≈D-sym (r :: eq) = sym r :: ≈D-sym eq

≈D-trans : forall {n} {D D' D'' : Ctx n} -> D ≈D D' -> D' ≈D D'' -> D ≈D D''
≈D-trans nil nil = nil
≈D-trans (r :: eq) (r' :: eq') = trans r r' :: ≈D-trans eq eq'

constQCtx : forall n -> C -> QCtx n
constQCtx zero rho = nil
constQCtx (succ n) rho = rho :: constQCtx n rho

varQCtx : forall {n} -> 1 ≤th n -> C -> QCtx n
varQCtx (os th) rho = rho :: constQCtx _ rho
varQCtx (o' th) rho = e0 :: varQCtx th rho

infix 4 _≈G_ _≤G_

_≈G_ : forall {n} (G' G : QCtx n) -> Set _
_≈G_ = VZip _==_

≈G-refl : forall {n} (G : QCtx n) -> G ≈G G
≈G-refl nil = nil
≈G-refl (p :: G) = refl :: ≈G-refl G

_≤G_ : forall {n} (G' G : QCtx n) -> Set _
_≤G_ = VZip _≤_

≤G-refl : forall {n} (G : QCtx n) -> G ≤G G
≤G-refl nil = nil
≤G-refl (p :: G) = ≤-refl :: ≤G-refl G

≤G-reflexive : forall {n} {G0 G1 : QCtx n} -> G0 ≈G G1 -> G0 ≤G G1
≤G-reflexive nil = nil
≤G-reflexive (eq :: eqs) = ≤-reflexive eq :: ≤G-reflexive eqs

≤G-trans : forall {n} {G0 G1 G2 : QCtx n} -> G0 ≤G G1 -> G1 ≤G G2 -> G0 ≤G G2
≤G-trans nil nil = nil
≤G-trans (le01 :: sub01) (le12 :: sub12) = ≤-trans le01 le12 :: ≤G-trans sub01 sub12

infixl 5 _+G_
infixl 6 _*G_

_+G_ : forall {n} (G0 G1 : QCtx n) -> QCtx n
_+G_ = vzip _+_

_*G_ : forall {n} -> C -> QCtx n -> QCtx n
_*G_ rho = vmap (rho *_)

meetG : forall {n} (G0 G1 : QCtx n) -> QCtx n
meetG = vzip meet

lowerBoundG : forall {n} -> ((G0 G1 : QCtx n) -> meetG G0 G1 ≤G G0)
                          × ((G0 G1 : QCtx n) -> meetG G0 G1 ≤G G1)
lowerBoundG = f , s
  where
  f : forall {n} (G0 G1 : QCtx n) -> meetG G0 G1 ≤G G0
  f nil nil = nil
  f (p0 :: G0) (p1 :: G1) = fst lowerBound p0 p1 :: f G0 G1

  s : forall {n} (G0 G1 : QCtx n) -> meetG G0 G1 ≤G G1
  s nil nil = nil
  s (p0 :: G0) (p1 :: G1) = snd lowerBound p0 p1 :: s G0 G1

greatestG : forall {n} {G0 G1 G : QCtx n} ->
            G ≤G G0 -> G ≤G G1 -> G ≤G meetG G0 G1
greatestG {G0 = nil} {nil} {nil} nil nil = nil
greatestG {G0 = _ :: _} {_ :: _} {_ :: _} (le0 :: sub0) (le1 :: sub1) =
  greatest le0 le1 :: greatestG sub0 sub1

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

infix 3 _|-_∈_ _|-_∋_ _|-[_]_ _|-[_]_∈ _|-[_]∋_

-- type correctness
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

-- untyped resource correctness
data _|-[_]_ {n} (G : QCtx n) (sg : Two) : forall {d} -> Term n d -> Set (l' ⊔ c) where
  var : forall {th}
        (sub : G ≤G varQCtx th (sg->rho sg))
        ->
        G |-[ sg ] var th
  app : forall {Ge Gs e s}
        (split : G ≈G Ge +G Gs)
        (er : Ge |-[ sg ] e) (sr : Gs |-[ sg ] s)
        ->
        G |-[ sg ] app e s
  proj0 : forall {e}
          (er : G |-[ sg ] e)
          ->
          G |-[ sg ] proj0 e
  proj1 : forall {e}
          (er : G |-[ sg ] e)
          ->
          G |-[ sg ] proj1 e
  the : forall {S s}
        (sr : G |-[ sg ] s)
        ->
        G |-[ sg ] the S s

  lam : forall {s}
        (sr : sg->rho sg :: G |-[ sg ] s)
        ->
        G |-[ sg ] lam s
  ten : forall {G0 G1 s0 s1}
        (split : G ≈G G0 +G G1)
        (s0r : G0 |-[ sg ] s0) (s1r : G1 |-[ sg ] s1)
        ->
        G |-[ sg ] ten s0 s1
  pm : let sg' = sg->rho sg in
       forall {Ge Gs e s}
       (split : G ≈G Ge +G Gs)
       (er : Ge |-[ sg ] e) (sr : sg' :: sg' :: Gs |-[ sg ] s)
       ->
       G |-[ sg ] pm e s
  wth : forall {s0 s1}
        (s0r : G |-[ sg ] s0) (s1r : G |-[ sg ] s1)
        ->
        G |-[ sg ] wth s0 s1
  inj0 : forall {s}
         (sr : G |-[ sg ] s)
         ->
         G |-[ sg ] inj0 s
  inj1 : forall {s}
         (sr : G |-[ sg ] s)
         ->
         G |-[ sg ] inj1 s
  case : let sg' = sg->rho sg in
         forall {Ge Gs e s0 s1}
         (split : G ≈G Ge +G Gs)
         (er : Ge |-[ sg ] e) (s0r : sg' :: Gs |-[ sg ] s0) (s1r : sg' :: Gs |-[ sg ] s1)
         ->
         G |-[ sg ] case e s0 s1
  bang : forall {Gs rho s}
         (split : G ≈G rho *G Gs)
         (sr : Gs |-[ sg ] s)
         ->
         G |-[ sg ] bang s
  [_] : forall {e}
        (er : G |-[ sg ] e)
        ->
        G |-[ sg ] [ e ]

-- resource correctness of typed terms (may not be a good idea)
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
        (er : Ge |-[ sg ] et ∈) (sr : Gs |-[ sg ]∋ st)
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

1≤th-indexCong : forall {n} {D D' : Ctx n} th -> D ≈D D' -> 1≤th-index th D == 1≤th-index th D'
1≤th-indexCong (os th) (r :: eq) = r
1≤th-indexCong (o' th) (r :: eq) = 1≤th-indexCong th eq

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

GoodSums : Set _
GoodSums =
  forall {a b c'} -> c' ≤ (a + b) ->
  Sgi _ \ a' -> Sgi _ \ b' -> (a' ≤ a) × (b' ≤ b) × (c' == (a' + b'))

GoodProducts : Set _
GoodProducts =
  forall {a b c'} -> c' ≤ (a * b) ->
  Sgi _ \ b' -> (b' ≤ b) × (c' == (a * b'))

splitSumQCtx : forall {n} {G0 G1 G' : QCtx n} ->
               GoodSums -> G' ≤G (G0 +G G1) ->
               Sgi _ \ G0' -> Sgi _ \ G1' -> (G0' ≤G G0) × (G1' ≤G G1) × (G' ≈G (G0' +G G1'))
splitSumQCtx {G0 = nil} {nil} {nil} gs nil = -, -, nil , nil , nil
splitSumQCtx {G0 = p0 :: G0} {p1 :: G1} {p' :: G'} gs (le :: sub) with gs le | splitSumQCtx gs sub
... | -, -, le0 , le1 , eq | -, -, sub0 , sub1 , eqs =
  -, -, le0 :: sub0 , le1 :: sub1 , eq :: eqs

splitProductQCtx : forall {n rho} {G0 G' : QCtx n} ->
                   GoodProducts -> G' ≤G (rho *G G0) ->
                   Sgi _ \ G0' -> (G0' ≤G G0) × (G' ≈G (rho *G G0'))
splitProductQCtx {G0 = nil} {nil} gp nil = -, nil , nil
splitProductQCtx {G0 = p0 :: G0} {p' :: G'} gp (le :: sub) with gp le | splitProductQCtx gp sub
... | -, le0 , eq | -, sub0 , eqs = -, le0 :: sub0 , eq :: eqs

module GoodStuff (gs : GoodSums) (gp : GoodProducts) (_≤?_ : forall x y -> Dec (x ≤ y)) where

  weakenRes : forall {n d G G'} {t : Term n d} {sg} ->
              G' ≤G G -> G |-[ sg ] t -> G' |-[ sg ] t
  weakenRes sub (var vsub) = var (≤G-trans sub vsub)
  weakenRes sub (app split er sr)
    with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
  ... | -, -, sube , subs , split' =
    app split' (weakenRes sube er) (weakenRes subs sr)
  weakenRes sub (proj0 er) = proj0 (weakenRes sub er)
  weakenRes sub (proj1 er) = proj1 (weakenRes sub er)
  weakenRes sub (the sr) = the (weakenRes sub sr)
  weakenRes sub (lam sr) = lam (weakenRes (≤-refl :: sub) sr)
  weakenRes sub (ten split s0r s1r)
    with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
  ... | -, -, sub0 , sub1 , split' =
    ten split' (weakenRes sub0 s0r) (weakenRes sub1 s1r)
  weakenRes sub (pm split er sr)
    with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
  ... | -, -, sube , subs , split' =
    pm split' (weakenRes sube er) (weakenRes (≤-refl :: ≤-refl :: subs) sr)
  weakenRes sub (wth s0r s1r) = wth (weakenRes sub s0r) (weakenRes sub s1r)
  weakenRes sub (inj0 sr) = inj0 (weakenRes sub sr)
  weakenRes sub (inj1 sr) = inj1 (weakenRes sub sr)
  weakenRes sub (case split er s0r s1r)
    with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
  ... | -, -, sube , subs , split' =
    case split' (weakenRes sube er) (weakenRes (≤-refl :: subs) s0r) (weakenRes (≤-refl :: subs) s1r)
  weakenRes sub (bang split sr)
    with splitProductQCtx gp (≤G-trans sub (≤G-reflexive split))
  ... | -, subs , split' = bang split' (weakenRes subs sr)
  weakenRes sub [ er ] = [ weakenRes sub er ]

  {-+}
  inferRes : forall {n d} sg (t : Term n d) ->
             Sgi _ \ G -> G |-[ sg ] t
  inferRes sg (var th) = -, var (≤G-refl _)
  inferRes sg (app e s) = {!!}
  inferRes sg (proj0 e) = {!!}
  inferRes sg (proj1 e) = {!!}
  inferRes sg (the S s) = mapSgi the (inferRes sg s)
  inferRes sg (lam s) = {!!}
  inferRes sg (ten s0 s1) =
    let -,_ {G0} s0r = inferRes sg s0 in
    let -,_ {G1} s1r = inferRes sg s1 in
    -, ten (≈G-refl (G0 +G G1)) s0r s1r
  inferRes sg (pm e s) =
    let -,_ {Ge} er = inferRes sg e in
    let -,_ {Gs} sr = inferRes sg s in
    -, ten (≈G-refl (Ge +G Gs)) er sr
  inferRes sg (wth s0 s1) =
    -, wth (weakenRes (fst lowerBoundG _ _) -$ (inferRes sg s0))
           (weakenRes (snd lowerBoundG _ _) -$ (inferRes sg s1))
  inferRes sg (inj0 s) = {!!}
  inferRes sg (inj1 s) = {!!}
  inferRes sg (case e s0 s1) = {!!}
  inferRes sg (bang s) = {!!}
  inferRes sg [ e ] = {!!}
  {+-}

  inferRes : forall {n d} sg (t : Term n d) ->
             Dec (Sgi _ \ G -> G |-[ sg ] t)
  inferRes sg (var th) = yes (-, var (≤G-refl _))
  inferRes sg (app e s) = {!!}
  inferRes sg (proj0 e) = {!!}
  inferRes sg (proj1 e) = {!!}
  inferRes sg (the S s) =
    mapDec (\ { (-, sr) -> -, the sr }) (\ { (-, the sr) -> -, sr }) (inferRes sg s)
  inferRes sg (lam s) =
    inferRes sg s >>=[ (\ { (-, lam sr) -> -, sr }) ] \ { (-,_ {p :: G} sr) ->
    mapDec (\ le -> -, lam (weakenRes (le :: ≤G-refl _) sr)) (\ { (-, lam sr') -> {!!}}) (sg->rho sg ≤? p) }
  inferRes sg (ten s0 s1) = {!!}
  inferRes sg (pm e s) = {!!}
  inferRes sg (wth s0 s1) =
    mapDec (\ { ((-, s0r) , (-, s1r)) -> -, wth (weakenRes (fst lowerBoundG _ _) s0r)
                                                (weakenRes (snd lowerBoundG _ _) s1r) })
           (\ { (-, wth s0r s1r) -> (-, s0r) , (-, s1r) })
           (inferRes sg s0 ×? inferRes sg s1)
  inferRes sg (inj0 s) = {!!}
  inferRes sg (inj1 s) = {!!}
  inferRes sg (case e s0 s1) = {!!}
  inferRes sg (bang s) = {!!}
  inferRes sg [ e ] = {!!}
