open import Setoid as Setoid'
open import Structure

module BidirectionalTiny {c l'} (C : Set c) (POS : Posemiring (==-Setoid C) l') where

open Posemiring POS

open import Common
  hiding (LTy; KEY; LIST; _<**>_; _&_; _-o_; Ctx)
  renaming (_*_ to _×_; _*?_ to _×?_; _*M_ to _×M_)
open import FunctionProperties
--open import Quantified S MSS using (QTy)
open Structure (==-Setoid C)

infixr 30 _~>_
data QTy : Set c where
  BASE : QTy
  _~>_ : QTy -> QTy -> QTy

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
varQCtx (os th) rho = rho :: constQCtx _ e0
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

1≤th-index-varQCtx :
  forall {n rho} (i : 1 ≤th n) -> 1≤th-index i (varQCtx i rho) == rho
1≤th-index-varQCtx (os i) = refl
1≤th-index-varQCtx (o' i) = 1≤th-index-varQCtx i

1≤th-index-constQCtx :
  forall {n rho} (i : 1 ≤th n) -> 1≤th-index i (constQCtx n rho) == rho
1≤th-index-constQCtx (os i) = refl
1≤th-index-constQCtx (o' i) = 1≤th-index-constQCtx i

1≤th-index-/=-varQCtx :
  forall {n rho} {i i' : 1 ≤th n} ->
  i' /= i -> 1≤th-index i' (varQCtx i rho) == e0
1≤th-index-/=-varQCtx {i = os i} {os i'} neq =
  Zero-elim (neq (cong os (z≤th-unique i' i)))
1≤th-index-/=-varQCtx {i = os i} {o' i'} neq = 1≤th-index-constQCtx i'
1≤th-index-/=-varQCtx {i = o' i} {os i'} neq = refl
1≤th-index-/=-varQCtx {i = o' i} {o' i'} neq =
  1≤th-index-/=-varQCtx (neq o cong o')

1≤th-insertVec-constQCtx :
  forall {n} (i : 1 ≤th succ n) rho ->
  1≤th-insertVec i rho (constQCtx n rho) ≈G constQCtx (succ n) rho
1≤th-insertVec-constQCtx (os i) rho = ≈G-refl _
1≤th-insertVec-constQCtx {zero} (o' i) rho = ≈G-refl _
1≤th-insertVec-constQCtx {succ n} (o' i) rho =
  refl :: 1≤th-insertVec-constQCtx i rho

1≤th-insertVec-varQCtx :
  forall {n} (i : 1 ≤th succ n) (j : 1 ≤th n) rho ->
  1≤th-insertVec i e0 (varQCtx j rho) ≈G varQCtx (punchIn i j) rho
1≤th-insertVec-varQCtx (os i) j rho = ≈G-refl _
1≤th-insertVec-varQCtx (o' i) (os j) rho =
  refl :: 1≤th-insertVec-constQCtx i e0
1≤th-insertVec-varQCtx (o' i) (o' j) rho =
  refl :: 1≤th-insertVec-varQCtx i j rho

un1≤th-insertVec-constQCtx :
  forall {n} i rho rho' G ->
  1≤th-insertVec i rho G ≤G constQCtx (succ n) rho' -> G ≤G constQCtx n rho'
un1≤th-insertVec-constQCtx (os i) rho rho' G (le :: sub) = sub
un1≤th-insertVec-constQCtx (o' i) rho rho' nil sub = nil
un1≤th-insertVec-constQCtx (o' i) rho rho' (p :: G) (le :: sub) =
  le :: un1≤th-insertVec-constQCtx i rho rho' G sub

un1≤th-insertVec-varQCtx :
  forall {n} i rho G ->
  1≤th-insertVec i rho G ≤G varQCtx i rho -> G ≤G constQCtx n e0
un1≤th-insertVec-varQCtx (os i) rho G (_ :: sub) = sub
un1≤th-insertVec-varQCtx (o' i) rho nil sub = nil
un1≤th-insertVec-varQCtx (o' i) rho (p :: G) (le :: sub) =
  le :: un1≤th-insertVec-varQCtx i rho G sub

un1≤th-insertVec-/=-varQCtx :
  forall {n i j} (neq : i /= j) rho G ->
  1≤th-insertVec i rho G ≤G varQCtx j rho -> G ≤G varQCtx {n} (punchOut neq) rho
un1≤th-insertVec-/=-varQCtx {i = os i} {os j} neq rho G (le :: sub) =
  Zero-elim (neq (cong os (z≤th-unique i j)))
un1≤th-insertVec-/=-varQCtx {i = os i} {o' j} neq rho G (le :: sub) = sub
un1≤th-insertVec-/=-varQCtx {i = o' ()} {j} neq rho nil sub
un1≤th-insertVec-/=-varQCtx {i = o' i} {os j} neq rho (p :: G) (le :: sub) =
  le :: un1≤th-insertVec-constQCtx i rho e0 G sub
un1≤th-insertVec-/=-varQCtx {i = o' i} {o' j} neq rho (p :: G) (le :: sub) =
  le :: un1≤th-insertVec-/=-varQCtx (neq o cong o') rho G sub

1≤th-insertVec-/=-varQCtx-miss :
  forall {n i j} (neq : i /= j) rho G ->
  1≤th-insertVec i rho G ≤G varQCtx {succ n} j rho -> rho ≤ e0
1≤th-insertVec-/=-varQCtx-miss {i = os i} {os j} neq rho G sub =
  Zero-elim (neq (cong os (z≤th-unique i j)))
1≤th-insertVec-/=-varQCtx-miss {i = os i} {o' j} neq rho G (le :: sub) = le
1≤th-insertVec-/=-varQCtx-miss {i = o' ()} {os j} neq rho nil sub
1≤th-insertVec-/=-varQCtx-miss {i = o' i} {o' j} neq rho nil (le :: sub) = le
1≤th-insertVec-/=-varQCtx-miss {i = o' i} {os j} neq rho (p :: G) (le :: sub)
  with 1≤th-indexVZip i sub
... | r rewrite 1≤th-index-insertVec i rho G | 1≤th-index-constQCtx {rho = e0} i = r
1≤th-insertVec-/=-varQCtx-miss {i = o' i} {o' j} neq rho (p :: G) (le :: sub) =
  1≤th-insertVec-/=-varQCtx-miss (neq o cong o') rho G sub

infixl 5 _+G_
infixl 6 _*G_

_+G_ : forall {n} (G0 G1 : QCtx n) -> QCtx n
_+G_ = vzip _+_

_*G_ : forall {n} -> C -> QCtx n -> QCtx n
_*G_ rho = vmap (rho *_)

_+G-mono_ : forall {n} {G0 G0' G1 G1' : QCtx n} ->
            G0 ≤G G0' -> G1 ≤G G1' -> G0 +G G1 ≤G G0' +G G1'
nil +G-mono nil = nil
(le0 :: sub0) +G-mono (le1 :: sub1) = le0 +-mono le1 :: sub0 +G-mono sub1

_*G-mono_ : forall {n rho rho'} {G G' : QCtx n} ->
            rho ≤ rho' -> G ≤G G' -> rho *G G ≤G rho' *G G'
le *G-mono nil = nil
le *G-mono (leG :: sub) = le *-mono leG :: le *G-mono sub

+G-identity : (forall {n} G -> constQCtx n e0 +G G ≈G G)
            × (forall {n} G -> G +G constQCtx n e0 ≈G G)
fst +G-identity = go
  where
  go : forall {n} G -> constQCtx n e0 +G G ≈G G
  go nil = nil
  go (p :: G) = fst +-identity p :: go G
snd +G-identity = go
  where
  go : forall {n} G -> G +G constQCtx n e0 ≈G G
  go nil = nil
  go (p :: G) = snd +-identity p :: go G

+G-assoc : forall {n} (G G' G'' : QCtx n) ->
           (G +G G') +G G'' ≈G G +G (G' +G G'')
+G-assoc G G' G'' = {!!}

data Dir : Set where
  syn chk : Dir

data Term (n : Nat) : Dir -> Set c where
  var : (th : 1 ≤th n) -> Term n syn
  app : (e : Term n syn) (s : Term n chk) -> Term n syn
  the : (S : QTy) (s : Term n chk) -> Term n syn

  lam : (s : Term (succ n) chk) -> Term n chk
  [_] : (e : Term n syn) -> Term n chk

var# : forall {n} m {less : Auto (m <th? n)} -> Term n syn
var# m {less} = var (#th_ m {less})

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
  the : forall {S s}
        (st : D |- S ∋ s)
        ->
        D |- the S s ∈ S

data _|-_∋_ {n} (D : Ctx n) where
  lam : forall {s S T}
        (st : S :: D |- T ∋ s)
        ->
        D |- S ~> T ∋ lam s
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
        (split : G ≤G Ge +G Gs)
        (er : Ge |-[ sg ] e) (sr : Gs |-[ sg ] s)
        ->
        G |-[ sg ] app e s
  the : forall {S s}
        (sr : G |-[ sg ] s)
        ->
        G |-[ sg ] the S s

  lam : forall {s}
        (sr : sg->rho sg :: G |-[ sg ] s)
        ->
        G |-[ sg ] lam s
  [_] : forall {e}
        (er : G |-[ sg ] e)
        ->
        G |-[ sg ] [ e ]

1≤th-indexCong : forall {n} {D D' : Ctx n} th -> D ≈D D' -> 1≤th-index th D == 1≤th-index th D'
1≤th-indexCong (os th) (r :: eq) = r
1≤th-indexCong (o' th) (r :: eq) = 1≤th-indexCong th eq

module DecEq (_==?_ : (rho rho' : C) -> Dec (rho == rho')) where
  _==QTy?_ : (S S' : QTy) -> Dec (S == S')
  BASE ==QTy? BASE = yes refl
  BASE ==QTy? (S' ~> T') = no \ ()
  (S ~> T) ==QTy? BASE = no \ ()
  (S ~> T) ==QTy? (S' ~> T') =
    mapDec (\ { (refl , refl) -> refl })
           (\ { refl -> (refl , refl) })
           ((S ==QTy? S') ×? (T ==QTy? T'))

  Is~>? : forall S -> Dec (Sg _ \ S0 -> Sg _ \ S1 -> S0 ~> S1 == S)
  Is~>? BASE = no \ { (_ , _ , ()) }
  Is~>? (S0 ~> S1) = yes (S0 , S1 , refl)

  synthUnique : forall {n} {D : Ctx n} {e : Term n syn} {S S' : QTy} ->
                D |- e ∈ S -> D |- e ∈ S' -> S' == S
  synthUnique var var = refl
  synthUnique (app et st) (app et' st') with synthUnique et et'
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
  synthType D (the T s) = mapDec (\ st -> T , the st) (\ { (_ , the st) -> st }) (checkType D T s)

  checkType D S (lam s) with Is~>? S
  ... | no np = no (np o \ { (lam st) -> _ , _ , refl })
  ... | yes (S0 , S1 , refl) =
    mapDec lam (\ { (lam st) -> st }) (checkType (S0 :: D) S1 s)
  checkType D S [ e ] with synthType D e
  ... | no np = no (np o \ { [ et ] -> S , et })
  ... | yes (S' , et) = mapDec (\ { refl -> [ et ] }) (\ { [ et' ] → synthUnique et et' }) (S ==QTy? S')

--mapVars : forall {n d} (f g : Nat -> Nat) -> (forall {m} -> 1 ≤th f m -> 1 ≤th g m) -> Term (f n) d -> Term (g n) d
--mapVars f g h (var th) = var (h th)
--mapVars f g h (app e s) = {!!}
--mapVars f g h (the S s) = the S (mapVars f g h s)
--mapVars f g h (lam s) = lam {!mapVars f g h s!}
--mapVars f g h [ e ] = {!!}

punchInVars : forall {n d} -> 1 ≤th succ n -> Term n d -> Term (succ n) d
punchInVars i (var th) = var (punchIn i th)
punchInVars i (app e s) = app (punchInVars i e) (punchInVars i s)
punchInVars i (the S s) = the S (punchInVars i s)
punchInVars i (lam s) = lam (punchInVars (o' i) s)
punchInVars i [ e ] = [ punchInVars i e ]

substitute : forall {n d} -> 1 ≤th succ n -> QTy -> Term (succ n) d -> Term n chk -> Term n d
substitute i T (var th) t with i ==th? th
... | yes _ = the T t
... | no neq = var (punchOut neq)
substitute i T (app e s) t = app (substitute i T e t) (substitute i T s t)
substitute i T (the S s) t = the S (substitute i T s t)
substitute i T (lam s) t = lam (substitute (o' i) T s (punchInVars zeroth t))
substitute i T [ e ] t = [ substitute i T e t ]

data _~~>_ {n} : forall {d} (t u : Term n d) -> Set where
  beta : forall S T s0 s1 -> app (the (S ~> T) (lam s0)) s1 ~~> the T (substitute zeroth S s0 s1)
  upsilon : forall S s -> [ the S s ] ~~> s

punchInVars-ty-syn :
  forall {n D S T i} {e : Term n syn} ->
  D |- e ∈ T -> 1≤th-insertVec i S D |- punchInVars i e ∈ T
punchInVars-ty-chk :
  forall {n D S T i} {s : Term n chk} ->
  D |- T ∋ s -> 1≤th-insertVec i S D |- T ∋ punchInVars i s

punchInVars-ty-syn {D = D} {S} {i = i} (var {th})
  rewrite sym (1≤th-index-punchIn-insertVec i th S D) = var
punchInVars-ty-syn (app et st) = app (punchInVars-ty-syn et) (punchInVars-ty-chk st)
punchInVars-ty-syn (the st) = the (punchInVars-ty-chk st)

punchInVars-ty-chk (lam st) = lam (punchInVars-ty-chk st)
punchInVars-ty-chk [ et ] = [ punchInVars-ty-syn et ]

substitute-ty-syn :
  forall {n D S T} {e : Term (succ n) syn} {s : Term n chk} i ->
  1≤th-insertVec i S D |- e ∈ T -> D |- S ∋ s ->
  D |- substitute i S e s ∈ T
substitute-ty-chk :
  forall {n D S T} {s0 : Term (succ n) chk} {s1 : Term n chk} i ->
  1≤th-insertVec i S D |- T ∋ s0 -> D |- S ∋ s1 ->
  D |- T ∋ substitute i S s0 s1

substitute-ty-syn {D = D} {S} {e = var th} i var st with i ==th? th
... | yes refl rewrite 1≤th-index-insertVec th S D = the st
... | no neq rewrite 1≤th-index-/=-insertVec neq S D = var
substitute-ty-syn i (app et s0t) s1t =
  app (substitute-ty-syn i et s1t) (substitute-ty-chk i s0t s1t)
substitute-ty-syn i (the s0t) s1t = the (substitute-ty-chk i s0t s1t)

substitute-ty-chk i (lam s0t) s1t =
  lam (substitute-ty-chk (o' i) s0t (punchInVars-ty-chk s1t))
substitute-ty-chk i [ et ] st = [ substitute-ty-syn i et st ]

sg≤0->G≤0 :
  forall {n d G sg} {t : Term n d} ->
  G |-[ sg ] t -> sg->rho sg ≤ e0 -> G ≤G constQCtx n e0
sg≤0->G≤0 {sg = sg} (var {th = th} sub) le = go th sub
  where
  go : forall {n G} th -> G ≤G varQCtx th (sg->rho sg) -> G ≤G constQCtx n e0
  go (os th) (le' :: sub) = ≤-trans le' le :: sub
  go (o' th) (le' :: sub) = le' :: go th sub
sg≤0->G≤0 (app split er sr) le =
  ≤G-trans split
           (≤G-trans (sg≤0->G≤0 er le +G-mono sg≤0->G≤0 sr le)
                     (≤G-reflexive (fst +G-identity _)))
sg≤0->G≤0 (the sr) le = sg≤0->G≤0 sr le
sg≤0->G≤0 (lam sr) le = tailVZip (sg≤0->G≤0 sr le)
sg≤0->G≤0 [ er ] le = sg≤0->G≤0 er le

punchInVars-res :
  forall {n d G sg i} {t : Term n d} ->
  G |-[ sg ] t -> 1≤th-insertVec i e0 G |-[ sg ] punchInVars i t
punchInVars-res {sg = sg} {i = i} (var {th = th} sub)
  with 1≤th-insertVZip i (≤-refl {x = e0}) sub
... | r rewrite VZip== (1≤th-insertVec-varQCtx i th (sg->rho sg)) = var r
punchInVars-res {G = G} {i = i} (app {Ge = Ge} {Gs} split er sr)
  with 1≤th-insertVec-vzip i _+_ e0 e0 Ge Gs
... | lemma rewrite fst +-identity e0 =
  app (≤G-trans (1≤th-insertVZip i (≤-refl {x = e0}) split)
                (≤G-reflexive (==VZip lemma)))
      (punchInVars-res er)
      (punchInVars-res sr)
punchInVars-res (the sr) = the (punchInVars-res sr)
punchInVars-res (lam sr) = lam (punchInVars-res sr)
punchInVars-res [ er ] = [ punchInVars-res er ]

module DecLE (_≤?_ : forall x y -> Dec (x ≤ y)) where

  weakenRes : forall {n d G G'} {t : Term n d} {sg} ->
              G' ≤G G -> G |-[ sg ] t -> G' |-[ sg ] t
  weakenRes sub (var vsub) = var (≤G-trans sub vsub)
  weakenRes sub (app split er sr) = app (≤G-trans sub split) er sr
  weakenRes sub (the sr) = the (weakenRes sub sr)
  weakenRes sub (lam sr) = lam (weakenRes (≤-refl :: sub) sr)
  weakenRes sub [ er ] = [ weakenRes sub er ]

  inferRes : forall {n d} sg (t : Term n d) ->
             Maybe (Sg _ \ G -> G |-[ sg ] t × forall {G'} -> G' |-[ sg ] t -> G' ≤G G)
  inferRes sg (var th) = just (_ , var (≤G-refl _) , \ { (var th') -> th' })
  inferRes sg (app e s) =
    mapMaybe (\ { ((Ge , er , eb) , (Gs , sr , sb)) ->
                Ge +G Gs
                , app (≤G-refl _) er sr
                , \ { (app split' er' sr') -> ≤G-trans split' (eb er' +G-mono sb sr') } })
             (inferRes sg e ×M inferRes sg s)
  inferRes sg (the S s) = mapMaybe (mapSg id (mapSg the \ b -> \ { (the sr) -> b sr })) (inferRes sg s)
  inferRes sg (lam s) =
    inferRes sg s                   >>= \ { (rhos :: G , sr , sb) ->
    Dec->Maybe (sg->rho sg ≤? rhos) >>= \ le ->
    just (_ , lam (weakenRes (le :: ≤G-refl _) sr) , \ { (lam sr') -> tailVZip (sb sr') }) }
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
  inferResComplete sg (the S s) (the sr) with inferResComplete sg s sr
  ... | G' , sr' , sb' , eq rewrite eq = _ , _ , _ , refl
  inferResComplete sg (lam s) (lam sr) with inferResComplete sg s sr
  ... | rhos' :: G' , sr' , sb' , eq rewrite eq with sg->rho sg ≤? rhos'
  ... | yes p = _ , _ , _ , refl
  ... | no np = Zero-elim (np (headVZip (sb' sr)))
  inferResComplete sg [ e ] [ er ] with inferResComplete sg e er
  ... | G' , er' , eb' , eq rewrite eq = _ , _ , _ , refl

  bestRes? : forall {n d} sg (t : Term n d) ->
             Dec (Sg _ \ G -> G |-[ sg ] t × forall {G'} -> G' |-[ sg ] t -> G' ≤G G)
  bestRes? sg t with inferRes sg t | inspect (inferRes sg) t
  ... | just p | _ = yes p
  ... | nothing | ingraph eq =
    no \ { (_ , r , _) ->
         nothing/=just (trans (sym eq) (snd (snd (snd (inferResComplete sg t r))))) }

  substitute-res' :
    forall {n d G Gt Gs sg rho S i} {t : Term (succ n) d} {s : Term n chk} ->
    G ≤G Gt +G Gs -> 1≤th-insertVec i rho Gt |-[ sg ] t -> Gs |-[ sg ] s ->
    G |-[ sg ] substitute i S t s
  substitute-res' split (var sub) sr = {!!}
  substitute-res' {G = G} {Gt = Ge} {Gs = Gs} {rho = rho} {S = S} {i = i} split (app {Ge'} {Gs'} split' e'r s'r) sr
    with 1≤th-index i Ge' | mapSg id VZip== (is-1≤th-insertVec i Ge')
       | 1≤th-index i Gs' | mapSg id VZip== (is-1≤th-insertVec i Gs')
  ... | rhoe | Ge'' , refl | rhos | Gs'' , refl
    rewrite sym (1≤th-insertVec-vzip i _+_ rhoe rhos Ge'' Gs'') with 1≤th-removeVZip i split'
  ... | split'' rewrite VZip== (1≤th-removeVec-insertVec i rho Ge)
                      | VZip== (1≤th-removeVec-insertVec i (rhoe + rhos) (Ge'' +G Gs''))
    =
    let fooe = substitute-res' {G = {!!}} {rho = rhoe} {S = S} {i = i} {!!} e'r sr in
    let foos = substitute-res' {G = {!!}} {rho = rhos} {S = S} {i = i} {!!} s'r sr in
    app (≤G-trans split (split'' +G-mono ≤G-refl _)) fooe foos
  substitute-res' split (the s'r) sr = the (substitute-res' split s'r sr)
  substitute-res' split (lam s'r) sr = {!!}
  substitute-res' split [ er ] sr = [ substitute-res' split er sr ]

  substitute-res :
    forall {n d G Gt Gs sg S i} {t : Term (succ n) d} {s : Term n chk} ->
    G ≤G Gt +G Gs -> 1≤th-insertVec i (sg->rho sg) Gt |-[ sg ] t -> Gs |-[ sg ] s ->
    G |-[ sg ] substitute i S t s
  substitute-res {i = i} split (var {th = th} sub) tr with i ==th? th
  ... | yes refl =
    the (weakenRes (≤G-trans split
                             (≤G-trans (un1≤th-insertVec-varQCtx th _ _ sub +G-mono ≤G-refl _)
                                       (≤G-reflexive (fst +G-identity _))))
                   tr)
  ... | no neq =
    let sg≤0 = 1≤th-insertVec-/=-varQCtx-miss neq _ _ sub in
    var (≤G-trans split
                  (≤G-trans (≤G-refl _ +G-mono sg≤0->G≤0 tr sg≤0)
                            (≤G-trans (≤G-reflexive (snd +G-identity _))
                                      (un1≤th-insertVec-/=-varQCtx neq _ _ sub))))
  substitute-res {n} {d} {G = G} {Ge} {Gs} {sg} {S = S} {i} {app e' s'} {s} split (app {Ge'} {Gs'} split' e'r s'r) sr =
    -- use 1≤th-removeVec-insertVec on split'
    let foo = substitute-res {Gt = 1≤th-removeVec i Gs'} {Gs = {!1≤th-removeVZip i split'!}} {S = S} {i = i} {t = s'} {s = s} {!!} (weakenRes {!1≤th-indexVZip i split'!} s'r) sr in
    {!!}
    --{!_|-[_]_.app {G = G} ? (substitute-res {S = S} {i} ? e0r tr) (substitute-res ? s0r tr)!}
    where
    bar : Sg _ \ Ge'' -> Ge' == 1≤th-insertVec i (1≤th-index i Ge') Ge''
    bar = {!!}
  substitute-res split (the s0r) tr = the (substitute-res split s0r tr)
  substitute-res split (lam s0r) tr =
    lam (substitute-res (≤-reflexive (sym (snd +-identity _)) :: split) s0r (punchInVars-res tr))
  substitute-res split [ e0r ] tr = [ substitute-res split e0r tr ]

  ~~>-preserves-res : forall {n d G sg} {t u : Term n d} {tr : G |-[ sg ] t} ->
                      t ~~> u -> G |-[ sg ] u
  ~~>-preserves-res {t = .(app (the (S ~> T) (lam s0)) s1)} {.(the T (substitute (os (z≤th _)) S s0 s1))} {app split (the (lam s0r)) s1r} (beta S T s0 s1) = the (substitute-res split s0r s1r)
  ~~>-preserves-res {t = .([ the S s ])} {.s} {[ the tr ]} (upsilon S s) = tr
