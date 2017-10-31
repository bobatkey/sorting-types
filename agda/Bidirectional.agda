open import Setoid as Setoid'
open import Structure

module Bidirectional {c} {x : Set} {l'} (C : Set c) (X : Set) (MSS : MeetSemilatticeSemiring (==-Setoid C) l') where

open MeetSemilatticeSemiring MSS

open import Common
  hiding (LTy; KEY; LIST; _<**>_; _&_; _-o_; Ctx)
  renaming (_*_ to _×_; _*?_ to _×?_; _*M_ to _×M_)
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
QCtx = Vec {c} C

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

_+G-mono_ : forall {n} {G0 G0' G1 G1' : QCtx n} ->
            G0 ≤G G0' -> G1 ≤G G1' -> G0 +G G1 ≤G G0' +G G1'
nil +G-mono nil = nil
(le0 :: sub0) +G-mono (le1 :: sub1) = le0 +-mono le1 :: sub0 +G-mono sub1

data Dir : Set where
  syn chk : Dir

data Term (n : Nat) : Dir -> Set c where
  var : (th : 1 ≤th n) -> Term n syn
  app : (e : Term n syn) (s : Term n chk) -> Term n syn
  pm : (U : QTy) (e : Term n syn) (s : Term (succ (succ n)) chk) -> Term n syn
  proj0 proj1 : (e : Term n syn) -> Term n syn
  case : (U : QTy) (e : Term n syn) (s0 s1 : Term (succ n) chk) -> Term n syn
  bm : (T : QTy) (e : Term n syn) (s : Term (succ n) chk) -> Term n syn
  the : (T : QTy) (s : Term n chk) -> Term n syn

  lam : (s : Term (succ n) chk) -> Term n chk
  ten : (s0 s1 : Term n chk) -> Term n chk
  wth : (s0 s1 : Term n chk) -> Term n chk
  inj0 inj1 : (s : Term n chk) -> Term n chk
  bang : (rho : C) (s : Term n chk) -> Term n chk
  [_] : (e : Term n syn) -> Term n chk

infix 3 _|-_∈_ _|-_∋_ _|-[_]_ --_|-[_]_∈ _|-[_]∋_

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
  pm : forall {e s S T U}
       (et : D |- e ∈ S <**> T) (st : T :: S :: D |- U ∋ s)
       ->
       D |- pm U e s ∈ U
  proj0 : forall {e S T}
          (et : D |- e ∈ S & T)
          ->
          D |- proj0 e ∈ S
  proj1 : forall {e S T}
          (et : D |- e ∈ S & T)
          ->
          D |- proj1 e ∈ T
  case : forall {e s0 s1 S T U}
         (et : D |- e ∈ S || T) (s0t : S :: D |- U ∋ s0) (s1t : T :: D |- U ∋ s1)
         ->
         D |- case U e s0 s1 ∈ U
  bm : forall {e s rho S T}
       (et : D |- e ∈ BANG rho S) (st : S :: D |- T ∋ s)
       ->
       D |- bm T e s ∈ T
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
  bang : forall {s S rho}
         (st : D |- S ∋ s)
         ->
         D |- BANG rho S ∋ bang rho s
  [_] : forall {e S}
        (et : D |- e ∈ S)
        ->
        D |- S ∋ [ e ]

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
  pm : let sg' = sg->rho sg in
       forall {Ge Gs U e s}
       (split : G ≈G Ge +G Gs)
       (er : Ge |-[ sg ] e) (sr : sg' :: sg' :: Gs |-[ sg ] s)
       ->
       G |-[ sg ] pm U e s
  proj0 : forall {e}
          (er : G |-[ sg ] e)
          ->
          G |-[ sg ] proj0 e
  proj1 : forall {e}
          (er : G |-[ sg ] e)
          ->
          G |-[ sg ] proj1 e
  case : let sg' = sg->rho sg in
         forall {Ge Gs U e s0 s1}
         (split : G ≈G Ge +G Gs)
         (er : Ge |-[ sg ] e) (s0r : sg' :: Gs |-[ sg ] s0) (s1r : sg' :: Gs |-[ sg ] s1)
         ->
         G |-[ sg ] case U e s0 s1
  bm : forall {Ge Gs T e s rho}
       (split : G ≈G Ge +G Gs)
       (er : Ge |-[ sg ] e) (sr : sg->rho sg * rho :: Gs |-[ sg ] s)
       ->
       G |-[ sg ] bm T e s
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
  bang : forall {Gs rho s}
         (split : G ≈G rho *G Gs)
         (sr : Gs |-[ sg ] s)
         ->
         G |-[ sg ] bang rho s
  [_] : forall {e}
        (er : G |-[ sg ] e)
        ->
        G |-[ sg ] [ e ]

1≤th-indexCong : forall {n} {D D' : Ctx n} th -> D ≈D D' -> 1≤th-index th D == 1≤th-index th D'
1≤th-indexCong (os th) (r :: eq) = r
1≤th-indexCong (o' th) (r :: eq) = 1≤th-indexCong th eq

GoodSums : Set _
GoodSums =
  forall {a b c'} -> c' ≤ (a + b) ->
  Sg _ \ a' -> Sg _ \ b' -> (a' ≤ a) × (b' ≤ b) × (c' == (a' + b'))

GoodProducts : Set _
GoodProducts =
  forall {a b c'} -> c' ≤ (a * b) ->
  Sg _ \ b' -> (b' ≤ b) × (c' == (a * b'))

splitSumQCtx : forall {n} {G0 G1 G' : QCtx n} ->
               GoodSums -> G' ≤G (G0 +G G1) ->
               Sg _ \ G0' -> Sg _ \ G1' -> (G0' ≤G G0) × (G1' ≤G G1) × (G' ≈G (G0' +G G1'))
splitSumQCtx {G0 = nil} {nil} {nil} gs nil = _ , _ , nil , nil , nil
splitSumQCtx {G0 = p0 :: G0} {p1 :: G1} {p' :: G'} gs (le :: sub) with gs le | splitSumQCtx gs sub
... | _ , _ , le0 , le1 , eq | _ , _ , sub0 , sub1 , eqs =
  _ , _ , le0 :: sub0 , le1 :: sub1 , eq :: eqs

splitProductQCtx : forall {n rho} {G0 G' : QCtx n} ->
                   GoodProducts -> G' ≤G (rho *G G0) ->
                   Sg _ \ G0' -> (G0' ≤G G0) × (G' ≈G (rho *G G0'))
splitProductQCtx {G0 = nil} {nil} gp nil = _ , nil , nil
splitProductQCtx {G0 = p0 :: G0} {p' :: G'} gp (le :: sub) with gp le | splitProductQCtx gp sub
... | _ , le0 , eq | _ , sub0 , eqs = _ , le0 :: sub0 , eq :: eqs

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
  synthUnique (pm et st) (pm et' st') with synthUnique et et'
  ... | refl = refl
  synthUnique (proj0 et) (proj0 et') with synthUnique et et'
  ... | refl = refl
  synthUnique (proj1 et) (proj1 et') with synthUnique et et'
  ... | refl = refl
  synthUnique (case et s0t s1t) (case et' s0t' s1t') with synthUnique et et'
  ... | refl = refl
  synthUnique (bm et st) (bm et' st') with synthUnique et et'
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
  synthType D (pm U e s) =
    synthType D e               >>=[ (\ { (_ , pm et st) -> _ , et }) ] \ { (ST , et) ->
    Is<**>? ST                  >>=[ (\ { (_ , pm et' st') -> _ , _ , synthUnique et et' }) ]
                                \ { (S , T , refl) ->
    checkType (T :: S :: D) U s >>=[ inv et ] \ st ->
    yes (U , pm et st) } }
    where
    inv : forall {S T} -> D |- e ∈ S <**> T -> (Sg _ \ U' -> D |- pm U e s ∈ U') -> T :: S :: D |- U ∋ s
    inv et (_ , pm et' st') with synthUnique et et'
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
  synthType D (case U e s0 s1) =
    synthType D e           >>=[ (\ { (_ , case et _ _) -> _ , et }) ] \ { (ST , et) ->
    Is||? ST                >>=[ (\ { (_ , case et' _ _) -> _ , _ , synthUnique et et' }) ]
                            \ { (S , T , refl) ->
    checkType (S :: D) U s0 >>=[ fst o inv et ] \ s0t ->
    checkType (T :: D) U s1 >>=[ snd o inv et ] \ s1t ->
    yes (U , case et s0t s1t)} }
    where
    inv : forall {S T} -> D |- e ∈ S || T -> (Sg _ \ U' -> D |- case U e s0 s1 ∈ U') ->
          S :: D |- U ∋ s0 × T :: D |- U ∋ s1
    inv et (_ , case et' s0t' s1t') with synthUnique et et'
    ... | refl = s0t' , s1t'
  synthType D (bm T e s) =
    synthType D e          >>=[ (\ { (_ , bm et _) -> _ , et }) ] \ { (S' , et) ->
    IsBANG? S'             >>=[ (\ { (_ , bm et' _) -> _ , _ , synthUnique et et' }) ]
                           \ { (rho , S , refl) ->
    checkType (S :: D) T s >>=[ inv et ] \ st ->
    yes (T , bm et st) } }
    where
    inv : forall {rho S} -> D |- e ∈ BANG rho S -> (Sg _ \ T' -> D |- bm T e s ∈ T') -> S :: D |- T ∋ s
    inv et (_ , bm et' st') with synthUnique et et'
    ... | refl = st'
  synthType D (the T s) = mapDec (\ st -> T , the st) (\ { (_ , the st) -> st }) (checkType D T s)

  checkType D S (lam s) with Is~>? S
  ... | no np = no (np o \ { (lam st) -> _ , _ , refl })
  ... | yes (S0 , S1 , refl) =
    mapDec lam (\ { (lam st) -> st }) (checkType (S0 :: D) S1 s)
  checkType D ST (ten s0 s1) with Is<**>? ST
  ... | no np = no (np o \ { (ten s0t s1t) -> _ , _ , refl })
  ... | yes (S , T , refl) =
    mapDec (uncurry ten) (\ { (ten s0t s1t) -> s0t , s1t }) (checkType D S s0 ×? checkType D T s1)
  --checkType D U (pm e s) with synthType D e
  --... | no np = no (np o \ { (pm et' st') -> _ , et' })
  --... | yes (ST , et) with Is<**>? ST
  --...   | no np =
  --  no (np o \ { (pm et' st') -> _ , _ , synthUnique et et' })
  --...   | yes (S , T , refl) =
  --  mapDec (pm et) inv (checkType (T :: S :: D) U s)
  --  where
  --  inv : D |- U ∋ pm e s -> T :: S :: D |- U ∋ s
  --  inv (pm et' st') with synthUnique et et'
  --  ... | refl = st'
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
  --checkType D U (case e s0 s1) with synthType D e
  --... | no np = no (np o \ { (case et s0t s1t) -> _ , et })
  --... | yes (ST , et) with Is||? ST
  --...   | no np = no (np o \ { (case et' s0t' s1t') -> _ , _ , synthUnique et et' })
  --...   | yes (S , T , refl) =
  --  mapDec (uncurry (case et)) inv (checkType (S :: D) U s0 ×? checkType (T :: D) U s1)
  --  where
  --  inv : D |- U ∋ case e s0 s1 -> (S :: D |- U ∋ s0) × (T :: D |- U ∋ s1)
  --  inv (case et' s0t' s1t') with synthUnique et et'
  --  ... | refl = s0t' , s1t'
  checkType D S' (bang rho s) =
    IsBANG? S'      >>=[ (\ { (bang st) -> _ , _ , refl }) ] \ { (rho' , S , refl) ->
    rho' ==? rho    >>=[ (\ { (bang st) -> refl }) ] \ { refl ->
    checkType D S s >>=[ (\ { (bang st) -> st }) ] \ st ->
    yes (bang st) } }
  checkType D S [ e ] with synthType D e
  ... | no np = no (np o \ { [ et ] -> S , et })
  ... | yes (S' , et) = mapDec (\ { refl -> [ et ] }) (\ { [ et' ] → synthUnique et et' }) (S ==QTy? S')

  module GoodStuff (gs : GoodSums) (gp : GoodProducts) (_≤?_ : forall x y -> Dec (x ≤ y)) where

    weakenRes : forall {n d G G'} {t : Term n d} {sg} ->
                G' ≤G G -> G |-[ sg ] t -> G' |-[ sg ] t
    weakenRes sub (var vsub) = var (≤G-trans sub vsub)
    weakenRes sub (app split er sr)
      with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
    ... | _ , _ , sube , subs , split' =
      app split' (weakenRes sube er) (weakenRes subs sr)
    weakenRes sub (pm split er sr)
      with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
    ... | _ , _ , sube , subs , split' =
      pm split' (weakenRes sube er) (weakenRes (≤-refl :: ≤-refl :: subs) sr)
    weakenRes sub (proj0 er) = proj0 (weakenRes sub er)
    weakenRes sub (proj1 er) = proj1 (weakenRes sub er)
    weakenRes sub (case split er s0r s1r)
      with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
    ... | _ , _ , sube , subs , split' =
      case split' (weakenRes sube er) (weakenRes (≤-refl :: subs) s0r) (weakenRes (≤-refl :: subs) s1r)
    weakenRes sub (bm split er sr)
      with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
    ... | _ , _ , sube , subs , split' = bm split' (weakenRes sube er) (weakenRes (≤-refl :: subs) sr)
    weakenRes sub (the sr) = the (weakenRes sub sr)
    weakenRes sub (lam sr) = lam (weakenRes (≤-refl :: sub) sr)
    weakenRes sub (ten split s0r s1r)
      with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
    ... | _ , _ , sub0 , sub1 , split' =
      ten split' (weakenRes sub0 s0r) (weakenRes sub1 s1r)
    weakenRes sub (wth s0r s1r) = wth (weakenRes sub s0r) (weakenRes sub s1r)
    weakenRes sub (inj0 sr) = inj0 (weakenRes sub sr)
    weakenRes sub (inj1 sr) = inj1 (weakenRes sub sr)
    weakenRes sub (bang split sr)
      with splitProductQCtx gp (≤G-trans sub (≤G-reflexive split))
    ... | _ , subs , split' = bang split' (weakenRes subs sr)
    weakenRes sub [ er ] = [ weakenRes sub er ]

    inferRes : forall {n d} sg (t : Term n d) ->
               Maybe (Sg _ \ G -> G |-[ sg ] t)
    inferRes sg (var th) = just (_ , var (≤G-refl _))
    inferRes sg (app e s) =
      mapMaybe (\ { ((_ , er) , (_ , sr)) -> _ , app (≈G-refl _) er sr })
               (inferRes sg e ×M inferRes sg s)
    inferRes sg (pm U e s) =
      inferRes sg e                   >>= \ { (_ , er) ->
      inferRes sg s                   >>= \ { (rho0 :: rho1 :: Gs , sr) ->
      Dec->Maybe (sg->rho sg ≤? rho0) >>= \ le0 ->
      Dec->Maybe (sg->rho sg ≤? rho1) >>= \ le1 ->
      just (_ , pm (≈G-refl _) er (weakenRes (le0 :: le1 :: ≤G-refl _) sr)) } }
    inferRes sg (proj0 e) = mapMaybe (mapSg id proj0) (inferRes sg e)
    inferRes sg (proj1 e) = mapMaybe (mapSg id proj1) (inferRes sg e)
    inferRes sg (case U e s0 s1) =
      inferRes sg e                   >>= \ { (_ , er) ->
      inferRes sg s0                  >>= \ { (rho0 :: Gs0 , s0r) ->
      inferRes sg s1                  >>= \ { (rho1 :: Gs1 , s1r) ->
      Dec->Maybe (sg->rho sg ≤? rho0) >>= \ le0 ->
      Dec->Maybe (sg->rho sg ≤? rho1) >>= \ le1 ->
      just (_ , case (≈G-refl _) er (weakenRes (le0 :: fst lowerBoundG _ _) s0r)
                                    (weakenRes (le1 :: snd lowerBoundG _ _) s1r)) } } }
    inferRes sg (bm T e s) =
      inferRes sg e >>= \ { (_ , er) ->
      inferRes sg s >>= \ { (rho :: Gs , sr) ->
      conc sg er sr } }
      where
      conc : forall {Ge rho Gs} sg -> Ge |-[ sg ] e -> rho :: Gs |-[ sg ] s ->
             Maybe (Sg _ \ G -> G |-[ sg ] bm T e s)
      conc {Ge} {rho} {Gs} tt er sr =
        just (_ , bm (≈G-refl _) er (subst (\ z -> z :: Gs |-[ tt ] s) (sym (fst *-identity _)) sr))
      conc {Ge} {rho} {Gs} ff er sr =
        mapMaybe (\ { refl -> _ , bm (≈G-refl _) er (subst (\ z -> z :: Gs |-[ ff ] s)
                                                           (sym (fst annihil rho))
                                                           sr) })
                 (Dec->Maybe (rho ==? e0))
    inferRes sg (the T s) = mapMaybe (mapSg id the) (inferRes sg s)
    inferRes sg (lam s) =
      inferRes sg s                  >>= \ { (rho :: G , sr) ->
      Dec->Maybe (sg->rho sg ≤? rho) >>= \ le ->
      just (_ , lam (weakenRes (le :: ≤G-refl _) sr)) }
    inferRes sg (ten s0 s1) =
      mapMaybe (\ { ((_ , s0r) , (_ , s1r)) -> _ , ten (≈G-refl _) s0r s1r })
               (inferRes sg s0 ×M inferRes sg s1)
    inferRes sg (wth s0 s1) =
      mapMaybe (\ { ((_ , s0r) , (_ , s1r)) -> _ , wth (weakenRes (fst lowerBoundG _ _) s0r)
                                                       (weakenRes (snd lowerBoundG _ _) s1r) })
               (inferRes sg s0 ×M inferRes sg s1)
    inferRes sg (inj0 s) = mapMaybe (mapSg id inj0) (inferRes sg s)
    inferRes sg (inj1 s) = mapMaybe (mapSg id inj1) (inferRes sg s)
    inferRes sg (bang rho s) =
      mapMaybe (\ { (_ , sr) -> _ , bang (≈G-refl _) sr }) (inferRes sg s)
    inferRes sg [ e ] = mapMaybe (mapSg id [_]) (inferRes sg e)

    inferResBest : forall {n a sg} {t : Term n a} {G} tr -> inferRes sg t == just (G , tr) ->
                   forall {G'} -> G' |-[ sg ] t -> G' ≤G G
    inferResBest (var ._) refl (var sub') = sub'
    inferResBest {sg = sg} {app e s} (app split er sr) eq (app split' er' sr') with inferRes sg e
    inferResBest {sg = sg} {app e s} (app split er sr) () (app split' er' sr') | nothing
    inferResBest {sg = sg} {app e s} (app split er sr) eq (app split' er' sr') | just a with inferRes sg s
    inferResBest {sg = sg} {app e s} (app split er sr) () (app split' er' sr') | just a | nothing
    inferResBest {sg = sg} {app e s} (app ._ er sr) refl (app split' er' sr') | just (_ , _) | just (_ , _) =
      ≤G-trans (≤G-reflexive split') ({!inferResBest er ? er'!} +G-mono {!!})
    inferResBest (pm split er sr) eq (pm split' er' sr') = {!!}
    inferResBest (proj0 er) eq (proj0 er') = {!!}
    inferResBest (proj1 er) eq (proj1 er') = {!!}
    inferResBest (case split er s0r s1r) eq (case split' er' s0r' s1r') = {!!}
    inferResBest (bm split er sr) eq (bm split' er' sr') = {!!}
    inferResBest (the sr) eq (the sr') = {!!}
    inferResBest (lam sr) eq (lam sr') = {!!}
    inferResBest (ten split s0r s1r) eq (ten split' s0r' s1r') = {!!}
    inferResBest (wth s0r s1r) eq (wth s0r' s1r') = {!!}
    inferResBest (inj0 sr) eq (inj0 sr') = {!!}
    inferResBest (inj1 sr) eq (inj1 sr') = {!!}
    inferResBest (bang split sr) eq (bang split' sr') = {!!}
    inferResBest [ er ] eq [ er' ] = {!!}

    --inferResBest sg (var th) (var sub) = sub
    --inferResBest sg (app e s) = {!!}
    --inferResBest sg (pm U e s) = {!!}
    --inferResBest sg (proj0 e) with inferRes sg e | inferResBest sg e
    --... | just _ | r = \ { (proj0 er) -> r er }
    --... | nothing | r = r
    --inferResBest sg (proj1 e) with inferRes sg e | inferResBest sg e
    --... | just _ | r = \ { (proj1 er) -> r er }
    --... | nothing | r = r
    --inferResBest sg (case U e s0 s1) = {!!}
    --inferResBest sg (bm T e s) = {!!}
    --inferResBest sg (the S s) = {!!}
    --inferResBest sg (lam s) = {!QCtx!}
    --inferResBest sg (ten s0 s1) with inferRes sg s0 | inferRes sg s1 | inferResBest sg s0 | inferResBest sg s1 | ≤G-trans | ≤G-reflexive | _+G-mono_
    --... | just _ | just _ | r0 | r1 | ≤G-trans | ≤G-reflexive | _+G-mono_ =
    --  \ { (ten {G0 = G0} {G1} split s0r s1r) -> ≤G-trans (≤G-reflexive {!split!}) (r0 s0r +G-mono r1 s1r)
    --  }
    --... | just _ | nothing | r0 | r1 | _ | _ | _ = r1
    --... | nothing | b | r0 | r1 | _ | _ | _ = r0
    --inferResBest sg (wth s0 s1) = {!!}
    --inferResBest sg (inj0 s) with inferRes sg s --| inferResBest sg s
    --inferResBest sg (inj0 s) | just x = {!QCtx!}
    --inferResBest sg (inj0 s) | nothing = {!QCtx!} --lift {l = c ⊔ l'} <>
    --inferResBest sg (inj1 s) = {!help!}
    --inferResBest sg (bang rho s) = {!!}
    --inferResBest sg [ e ] = {!!}
