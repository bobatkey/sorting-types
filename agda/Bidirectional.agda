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

_*G-mono_ : forall {n rho rho'} {G G' : QCtx n} ->
            rho ≤ rho' -> G ≤G G' -> rho *G G ≤G rho' *G G'
le *G-mono nil = nil
le *G-mono (leG :: sub) = le *-mono leG :: le *G-mono sub

data Dir : Set where
  syn chk : Dir

data Term (n : Nat) : Dir -> Set c where
  var : (th : 1 ≤th n) -> Term n syn
  app : (e : Term n syn) (s : Term n chk) -> Term n syn
  pm : (U : QTy) (e : Term n syn) (s : Term (succ (succ n)) chk) -> Term n syn
  proj : (lr : Two) (e : Term n syn) -> Term n syn
  case : (U : QTy) (e : Term n syn) (s0 s1 : Term (succ n) chk) -> Term n syn
  bm : (T : QTy) (e : Term n syn) (s : Term (succ n) chk) -> Term n syn
  the : (T : QTy) (s : Term n chk) -> Term n syn

  lam : (s : Term (succ n) chk) -> Term n chk
  ten : (s0 s1 : Term n chk) -> Term n chk
  wth : (s0 s1 : Term n chk) -> Term n chk
  inj : (lr : Two) (s : Term n chk) -> Term n chk
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
  proj : forall {lr e S T}
         (et : D |- e ∈ S & T)
         ->
         D |- proj lr e ∈ if lr then S else T
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
  inj : forall {lr s S T}
        (st : D |- if lr then S else T ∋ s)
        ->
        D |- S || T ∋ inj lr s
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
  proj : forall {lr e}
         (er : G |-[ sg ] e)
         ->
         G |-[ sg ] proj lr e
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
  inj : forall {lr s}
        (sr : G |-[ sg ] s)
        ->
        G |-[ sg ] inj lr s
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
  synthUnique (proj et) (proj et') with synthUnique et et'
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
  synthType D (proj lr e) =
    -- testing out monadic-like syntax:
    -- test >>=[ if-fail ] \ success-evidence ->
    -- rest...
    synthType D e >>=[ (\ { (_ , proj et) -> _ , et }) ] \ { (S , et) ->
    Is&? S        >>=[ (\ { (_ , proj et') -> _ , _ , synthUnique et et' }) ] \ { (S0 , S1 , refl) ->
    yes (_ , proj et) } }
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
  checkType D S (wth s0 s1) with Is&? S
  ... | no np = no \ { (wth s0t s1t) -> np (_ , _ , refl) }
  ... | yes (S0 , S1 , refl) =
    mapDec (\ { (s0t , s1t) -> wth s0t s1t })
           (\ { (wth s0t s1t) -> s0t , s1t })
           (checkType D S0 s0 ×? checkType D S1 s1)
  checkType D ST (inj lr s) =
    Is||? ST >>=[ (\ { (inj st) -> _ , _ , refl }) ] \ { (S , T , refl) ->
    checkType D _ s >>=[ (\ { (inj st) -> st }) ]
    yes o inj }
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
    weakenRes sub (proj er) = proj (weakenRes sub er)
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
    weakenRes sub (inj sr) = inj (weakenRes sub sr)
    weakenRes sub (bang split sr)
      with splitProductQCtx gp (≤G-trans sub (≤G-reflexive split))
    ... | _ , subs , split' = bang split' (weakenRes subs sr)
    weakenRes sub [ er ] = [ weakenRes sub er ]

    inferRes : forall {n d} sg (t : Term n d) ->
               Maybe (Sg _ \ G -> G |-[ sg ] t × forall {G'} -> G' |-[ sg ] t -> G' ≤G G)
    inferRes sg (var th) = just (_ , var (≤G-refl _) , \ { (var th') -> th' })
    inferRes sg (app e s) =
      mapMaybe (\ { ((Ge , er , eb) , (Gs , sr , sb)) ->
                  Ge +G Gs
                  , app (≈G-refl _) er sr
                  , \ { (app split' er' sr') -> ≤G-trans (≤G-reflexive split') (eb er' +G-mono sb sr') } })
               (inferRes sg e ×M inferRes sg s)
    inferRes sg (pm U e s) =
      inferRes sg e                   >>= \ { (_ , er , eb) ->
      inferRes sg s                   >>= \ { (rho0 :: rho1 :: Gs , sr , sb) ->
      Dec->Maybe (sg->rho sg ≤? rho0) >>= \ le0 ->
      Dec->Maybe (sg->rho sg ≤? rho1) >>= \ le1 ->
      just (_ , pm (≈G-refl _) er (weakenRes (le0 :: le1 :: ≤G-refl _) sr)
           , \ { (pm split' er' sr') ->
               ≤G-trans (≤G-reflexive split') (eb er' +G-mono tailVZip (tailVZip (sb sr'))) }) } }
    inferRes sg (proj lr e) = mapMaybe (mapSg id (mapSg proj \ b -> \ { (proj er) -> b er })) (inferRes sg e)
    inferRes sg (case U e s0 s1) =
      inferRes sg e >>= \ { (Ge , er , eb) ->
      inferRes sg s0 >>= \ { (rho0 :: Gs0 , s0r , s0b) ->
      inferRes sg s1 >>= \ { (rho1 :: Gs1 , s1r , s1b) ->
      Dec->Maybe (sg->rho sg ≤? rho0) >>= \ le0 ->
      Dec->Maybe (sg->rho sg ≤? rho1) >>= \ le1 ->
      just (Ge +G meetG Gs0 Gs1
           , case (≈G-refl _) er (weakenRes (le0 :: fst lowerBoundG _ _) s0r)
                                 (weakenRes (le1 :: snd lowerBoundG _ _) s1r)
           , \ { (case split' er' s0r' s1r') ->
               ≤G-trans (≤G-reflexive split')
                        (eb er' +G-mono greatestG (tailVZip (s0b s0r'))
                                                  (tailVZip (s1b s1r'))) }) } } }
    inferRes sg (bm T e s) =
      inferRes sg e >>= \ { (_ , er , eb) ->
      inferRes sg s >>= \ { (rho :: Gs , sr , sb) ->
      conc sg er eb sr sb } }
      where
      conc : forall {Ge rho Gs} sg ->
             Ge |-[ sg ] e -> (forall {G'} -> G' |-[ sg ] e -> G' ≤G Ge) ->
             rho :: Gs |-[ sg ] s -> (forall {G'} -> G' |-[ sg ] s -> G' ≤G rho :: Gs) ->
             Maybe (Sg _ \ G -> Sg (G |-[ sg ] bm T e s) \ r -> forall {G'} -> G' |-[ sg ] bm T e s -> G' ≤G G)
      conc {Ge} {rho} {Gs} tt er eb sr sb =
        just (_ , bm (≈G-refl _) er (subst (\ z -> z :: Gs |-[ tt ] s) (sym (fst *-identity _)) sr)
             , \ { (bm split' er' sr') ->
                 ≤G-trans (≤G-reflexive split') (eb er' +G-mono tailVZip (sb sr')) })
      conc {Ge} {rho} {Gs} ff er eb sr sb =
        mapMaybe (\ le ->
                    _ , bm (≈G-refl _)
                           er
                           (weakenRes (≤-trans (≤-reflexive (fst annihil rho)) le :: ≤G-refl _) sr)
                    , \ { (bm split' er' sr') ->
                        ≤G-trans (≤G-reflexive split') (eb er' +G-mono tailVZip (sb sr')) })
                 (Dec->Maybe (e0 ≤? rho))
    inferRes sg (the S s) = mapMaybe (mapSg id (mapSg the \ b -> \ { (the sr) -> b sr })) (inferRes sg s)
    inferRes sg (lam s) =
      inferRes sg s                   >>= \ { (rhos :: G , sr , sb) ->
      Dec->Maybe (sg->rho sg ≤? rhos) >>= \ le ->
      just (_ , lam (weakenRes (le :: ≤G-refl _) sr) , \ { (lam sr') -> tailVZip (sb sr') }) }
    inferRes sg (ten s0 s1) =
      mapMaybe (\ { ((Gs0 , s0r , s0b) , (Gs1 , s1r , s1b)) ->
                  _ , ten (≈G-refl _) s0r s1r
                  , \ { (ten split' s0r' s1r') ->
                      ≤G-trans (≤G-reflexive split') (s0b s0r' +G-mono s1b s1r') } })
               (inferRes sg s0 ×M inferRes sg s1)
    inferRes sg (wth s0 s1) =
      mapMaybe (\ { ((Gs0 , s0r , s0b) , (Gs1 , s1r , s1b)) ->
                  meetG Gs0 Gs1
                  , wth (weakenRes (fst lowerBoundG _ _) s0r) (weakenRes (snd lowerBoundG _ _) s1r)
                  , \ { (wth s0r' s1r') -> greatestG (s0b s0r') (s1b s1r') } })
               (inferRes sg s0 ×M inferRes sg s1)
    inferRes sg (inj lr s) = mapMaybe (mapSg id (mapSg inj \ b -> \ { (inj sr) -> b sr })) (inferRes sg s)
    inferRes sg (bang rho s) =
      mapMaybe (mapSg _
                      (mapSg (bang (≈G-refl _))
                             \ sb -> \ { (bang split' sr') ->
                                         ≤G-trans (≤G-reflexive split') (≤-refl *G-mono sb sr') }))
               (inferRes sg s)
    inferRes sg [ e ] = mapMaybe (mapSg id (mapSg [_] \ b -> \ { ([ er ]) -> b er })) (inferRes sg e)

    -- interesting things happen where a variable is bound,
    -- i.e, where there is a possibility of failure
    inferResComplete : forall {n G d} sg (t : Term n d) -> G |-[ sg ] t ->
                       Sg _ \ G' ->
                       Sg (G' |-[ sg ] t) \ r' ->
                       Sg (forall {G''} -> G'' |-[ sg ] t -> G'' ≤G G') \ b' ->
                       inferRes sg t == just (G' , r' , b')
    inferResComplete sg (var th) (var sub) = _ , _ , _ , refl
    inferResComplete sg (app e s) (app split er sr)
      with inferResComplete sg e er | inferResComplete sg s sr
    ... | Ge' , er' , eb' , eeq | Gs' , sr' , sb' , seq rewrite eeq | seq = _ , _ , _ , refl
    inferResComplete sg (pm U e s) (pm split er sr)
      with inferResComplete sg e er | inferResComplete sg s sr
    ... | Ge' , er' , eb' , eeq | rho0' :: rho1' :: Gs' , sr' , sb' , seq rewrite eeq | seq
      with sg->rho sg ≤? rho0' | sg->rho sg ≤? rho1'
    ... | yes le0 | yes le1 = _ , _ , _ , refl
    ... | yes le0 | no nle1 = Zero-elim (nle1 (headVZip (tailVZip (sb' sr))))
    ... | no nle0 | _ = Zero-elim (nle0 (headVZip (sb' sr)))
    inferResComplete sg (proj lr e) (proj er) with inferResComplete sg e er
    ... | G' , er' , eb' , eq rewrite eq = _ , _ , _ , refl
    inferResComplete sg (case U e s0 s1) (case split er s0r s1r)
      with inferResComplete sg e er | inferResComplete sg s0 s0r | inferResComplete sg s1 s1r
    ... | Ge' , er' , eb' , eeq | rho0' :: Gs0' , s0r' , s0b' , s0eq | rho1' :: Gs1' , s1r' , s1b' , s1eq
      rewrite eeq | s0eq | s1eq with sg->rho sg ≤? rho0' | sg->rho sg ≤? rho1'
    ... | yes le0 | yes le1 = _ , _ , _ , refl
    ... | yes le0 | no nle1 = Zero-elim (nle1 (headVZip (s1b' s1r)))
    ... | no nle0 | _ = Zero-elim (nle0 (headVZip (s0b' s0r)))
    inferResComplete sg (bm T e s) (bm split er sr)
      with inferResComplete sg e er | inferResComplete sg s sr
    inferResComplete tt (bm T e s) (bm split er sr)
      | Ge' , er' , eb' , eeq | rhos' :: Gs' , sr' , sb' , seq
      rewrite eeq | seq = _ , _ , _ , refl
    inferResComplete ff (bm T e s) (bm split er sr)
      | Ge' , er' , eb' , eeq | rhos' :: Gs' , sr' , sb' , seq
      rewrite eeq | seq with e0 ≤? rhos'
    ... | yes p = _ , _ , _ , refl
    ... | no np = Zero-elim (np (≤-trans (≤-reflexive (sym (fst annihil _))) (headVZip (sb' sr))))
    inferResComplete sg (the S s) (the sr) with inferResComplete sg s sr
    ... | G' , sr' , sb' , eq rewrite eq = _ , _ , _ , refl
    inferResComplete sg (lam s) (lam sr) with inferResComplete sg s sr
    ... | rhos' :: G' , sr' , sb' , eq rewrite eq with sg->rho sg ≤? rhos'
    ... | yes p = _ , _ , _ , refl
    ... | no np = Zero-elim (np (headVZip (sb' sr)))
    inferResComplete sg (ten s0 s1) (ten split s0r s1r)
      with inferResComplete sg s0 s0r | inferResComplete sg s1 s1r
    ... | G0' , s0r' , s0b' , eq0 | G1' , s1r' , s1b' , eq1 rewrite eq0 | eq1 = _ , _ , _ , refl
    inferResComplete sg (wth s0 s1) (wth s0r s1r)
      with inferResComplete sg s0 s0r | inferResComplete sg s1 s1r
    ... | G0' , s0r' , s0b' , eq0 | G1' , s1r' , s1b' , eq1 rewrite eq0 | eq1 = _ , _ , _ , refl
    inferResComplete sg (inj lr s) (inj sr) with inferResComplete sg s sr
    ... | G' , sr' , sb' , eq rewrite eq = _ , _ , _ , refl
    inferResComplete sg (bang rho s) (bang split sr) with inferResComplete sg s sr
    ... | G' , sr' , sb' , eq rewrite eq = _ , _ , _ , refl
    inferResComplete sg [ e ] [ er ] with inferResComplete sg e er
    ... | G' , er' , eb' , eq rewrite eq = _ , _ , _ , refl
