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

varQCtx : forall {n} -> 1 ≤th n -> C -> QCtx n
varQCtx (os th) rho = rho :: replicateVec _ e0
varQCtx (o' th) rho = e0 :: varQCtx th rho

infix 4 _≈G_ _≤G_

_≈G_ : forall {n} (G' G : QCtx n) -> Set _
_≈G_ = VZip _==_

≈G-refl : forall {n} (G : QCtx n) -> G ≈G G
≈G-refl nil = nil
≈G-refl (p :: G) = refl :: ≈G-refl G

≈G-sym : forall {n} {G' G : QCtx n} -> G' ≈G G -> G ≈G G'
≈G-sym nil = nil
≈G-sym (r :: rs) = sym r :: ≈G-sym rs

≈G-trans : forall {n} {G G' G'' : QCtx n} -> G ≈G G' -> G' ≈G G'' -> G ≈G G''
≈G-trans nil nil = nil
≈G-trans (xy :: xys) (yz :: yzs) = trans xy yz :: ≈G-trans xys yzs

infixr 1 _≈[_]G_
infixr 2 _≈G-QED

_≈[_]G_ : forall {n} G {G' G'' : QCtx n} -> G ≈G G' -> G' ≈G G'' -> G ≈G G''
G ≈[ xy ]G yz = ≈G-trans xy yz

_≈G-QED : forall {n} (G : QCtx n) -> G ≈G G
G ≈G-QED = ≈G-refl G

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

infixr 1 _≤[_]G_
infixr 2 _≤G-QED

_≤[_]G_ : forall {n} G {G' G'' : QCtx n} -> G ≤G G' -> G' ≤G G'' -> G ≤G G''
G ≤[ xy ]G yz = ≤G-trans xy yz

_≤G-QED : forall {n} (G : QCtx n) -> G ≤G G
G ≤G-QED = ≤G-refl G

1≤th-index-varQCtx :
  forall {n rho} (i : 1 ≤th n) -> 1≤th-index i (varQCtx i rho) == rho
1≤th-index-varQCtx (os i) = refl
1≤th-index-varQCtx (o' i) = 1≤th-index-varQCtx i

1≤th-index-/=-varQCtx :
  forall {n} {i i' : 1 ≤th n} ->
  i' /= i -> (rho : C) -> 1≤th-index i' (varQCtx i rho) == e0
1≤th-index-/=-varQCtx {i = os i} {os i'} neq rho =
  Zero-elim (neq (cong os (z≤th-unique i' i)))
1≤th-index-/=-varQCtx {i = os i} {o' i'} neq rho = 1≤th-index-replicateVec i' e0
1≤th-index-/=-varQCtx {i = o' i} {os i'} neq rho = refl
1≤th-index-/=-varQCtx {i = o' i} {o' i'} neq rho =
  1≤th-index-/=-varQCtx (neq o cong o') rho

1≤th-insertVec-varQCtx :
  forall {n} (i : 1 ≤th succ n) (j : 1 ≤th n) rho ->
  1≤th-insertVec i e0 (varQCtx j rho) ≈G varQCtx (punchIn i j) rho
1≤th-insertVec-varQCtx (os i) j rho = ≈G-refl _
1≤th-insertVec-varQCtx (o' i) (os j) rho =
  refl :: 1≤th-insertVec-replicateVec i e0
1≤th-insertVec-varQCtx (o' i) (o' j) rho =
  refl :: 1≤th-insertVec-varQCtx i j rho

un1≤th-insertVec-replicateVec :
  forall {n} i rho rho' G ->
  1≤th-insertVec i rho G ≤G replicateVec (succ n) rho' -> G ≤G replicateVec n rho'
un1≤th-insertVec-replicateVec (os i) rho rho' G (le :: sub) = sub
un1≤th-insertVec-replicateVec (o' i) rho rho' nil sub = nil
un1≤th-insertVec-replicateVec (o' i) rho rho' (p :: G) (le :: sub) =
  le :: un1≤th-insertVec-replicateVec i rho rho' G sub

un1≤th-insertVec-varQCtx :
  forall {n} i rho G ->
  1≤th-insertVec i rho G ≤G varQCtx i rho -> G ≤G replicateVec n e0
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
  le :: un1≤th-insertVec-replicateVec i rho e0 G sub
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
... | r rewrite 1≤th-index-insertVec i rho G | 1≤th-index-replicateVec i e0 = r
1≤th-insertVec-/=-varQCtx-miss {i = o' i} {o' j} neq rho (p :: G) (le :: sub) =
  1≤th-insertVec-/=-varQCtx-miss (neq o cong o') rho G sub

varQCtx-part :
  forall l {m} (th : 1 ≤th l +N m) rho ->
  varQCtx th rho ≈G
    case 1≤th-part l th of \
    { (inl thl) -> varQCtx thl rho +V replicateVec m e0
    ; (inr thm) -> replicateVec l e0 +V varQCtx thm rho
    }
varQCtx-part zero th rho = ≈G-refl _
varQCtx-part (succ l) (os th) rho = refl :: replicateVec-+V l _ e0
varQCtx-part (succ l) (o' th) rho with 1≤th-part l th | varQCtx-part l th rho
varQCtx-part (succ l) (o' th) rho | inl thl | r = refl :: r
varQCtx-part (succ l) (o' th) rho | inr thm | r = refl :: r

varQCtx-leftPart :
  forall {m} n (th : 1 ≤th m) rho ->
  varQCtx (1≤th-leftPart n th) rho ≈G varQCtx th rho +V replicateVec n e0
varQCtx-leftPart {succ m} n (os th) rho = refl :: replicateVec-+V m n e0
varQCtx-leftPart {succ m} n (o' th) rho = refl :: varQCtx-leftPart n th rho

varQCtx-rightPart :
  forall m {n} (th : 1 ≤th n) rho ->
  varQCtx (1≤th-rightPart m th) rho ≈G replicateVec m e0 +V varQCtx th rho
varQCtx-rightPart zero th rho = ≈G-refl _
varQCtx-rightPart (succ m) th rho = refl :: varQCtx-rightPart m th rho

varQCtx-3parts :
  forall m {n} (th : 1 ≤th m +N succ n) rho -> 1≤thToNat th == m ->
  varQCtx th rho ≈G replicateVec m e0 +V rho :: replicateVec n e0
varQCtx-3parts zero (os th) rho refl = ≈G-refl _
varQCtx-3parts zero (o' th) rho ()
varQCtx-3parts (succ m) (os th) rho ()
varQCtx-3parts (succ m) (o' th) rho eq = refl :: varQCtx-3parts m th rho (succInj eq)

--varQCtx-punchOutN :
--  forall l {m} (th : 1 ≤th l +N m) (neq : 1≤thToNat th /= l) ->
--  varQCtx (punchOut l th neq) rho ≈G
--    case 1≤th-part l th of \
--    { (inl thl) -> varQCtx thl rho +V replicateVec m e0
--    ; (inr thm) -> replicateVec
--    }

infixl 6 _+G_ _+G-mono_ _+G-cong_
infixl 7 _*G_ _*G-mono_ _*G-cong_

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

_+G-cong_ : forall {n} {G0 G0' G1 G1' : QCtx n} ->
            G0 ≈G G0' -> G1 ≈G G1' -> G0 +G G1 ≈G G0' +G G1'
nil +G-cong nil = nil
(eq0 :: eqs0) +G-cong (eq1 :: eqs1) = (eq0 +-cong eq1) :: eqs0 +G-cong eqs1

_*G-cong_ : forall {n rho rho'} {G G' : QCtx n} ->
            rho == rho' -> G ≈G G' -> rho *G G ≈G rho' *G G'
eq *G-cong nil = nil
eq *G-cong (eqG :: eqs) = (eq *-cong eqG) :: eq *G-cong eqs

+G-identity : (forall {n} G -> replicateVec n e0 +G G ≈G G)
            × (forall {n} G -> G +G replicateVec n e0 ≈G G)
fst +G-identity = go
  where
  go : forall {n} G -> replicateVec n e0 +G G ≈G G
  go nil = nil
  go (p :: G) = fst +-identity p :: go G
snd +G-identity = go
  where
  go : forall {n} G -> G +G replicateVec n e0 ≈G G
  go nil = nil
  go (p :: G) = snd +-identity p :: go G

*G-identity : (forall {n} (G : QCtx n) -> e1 *G G ≈G G)
            × (forall {n} rho -> rho *G replicateVec n e1 ≈G replicateVec n rho)
fst *G-identity nil = nil
fst *G-identity (p :: G) = fst *-identity p :: fst *G-identity G

snd *G-identity {zero} rho = nil
snd *G-identity {succ n} rho = snd *-identity rho :: snd *G-identity {n} rho

+G-comm : forall {n} (G G' : QCtx n) -> G +G G' ≈G G' +G G
+G-comm nil nil = nil
+G-comm (p :: G) (p' :: G') = +-comm p p' :: +G-comm G G'

+G-assoc : forall {n} (G G' G'' : QCtx n) ->
           (G +G G') +G G'' ≈G G +G (G' +G G'')
+G-assoc nil nil nil = nil
+G-assoc (p :: G) (p' :: G') (p'' :: G'') = +-assoc p p' p'' :: +G-assoc G G' G''

*G-distrib-+ : forall {n} (G : QCtx n) (rho rho' : C) ->
               (rho + rho') *G G ≈G rho *G G +G rho' *G G
*G-distrib-+ nil rho rho' = nil
*G-distrib-+ (p :: G) rho rho' = snd distrib p rho rho' :: *G-distrib-+ G rho rho'

e0*G : forall {n} (G : QCtx n) -> e0 *G G ≈G replicateVec n e0
e0*G nil = nil
e0*G (p :: G) = fst annihil p :: e0*G G

*Gempty : forall rho n -> rho *G replicateVec n e0 ≈G replicateVec n e0
*Gempty rho n =
  rho *G replicateVec n e0   ≈[ vmap-replicateVec (rho *_) n e0 ]G
  replicateVec n (rho * e0)  ≈[ replicateVZip n (snd annihil rho) ]G
  replicateVec n e0          ≈G-QED

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

sg*sg==sg : forall sg -> sg->rho sg * sg->rho sg == sg->rho sg
sg*sg==sg tt = fst *-identity e1
sg*sg==sg ff = fst annihil e0

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

punchInNManyVars : forall {m d} n l -> Term (l +N m) d -> Term (l +N n +N m) d
punchInNManyVars n l (var th) = var (punchInNMany l n th)
punchInNManyVars n l (app e s) = app (punchInNManyVars n l e) (punchInNManyVars n l s)
punchInNManyVars n l (the S s) = the S (punchInNManyVars n l s)
punchInNManyVars n l (lam s) = lam (punchInNManyVars n (succ l) s)
punchInNManyVars n l [ e ] = [ punchInNManyVars n l e ]

Subst : Nat -> Nat -> Set c
Subst m n = 1 ≤th m -> Term n syn

liftSubst : forall {m n} -> Subst m n -> Subst (succ m) (succ n)
liftSubst vf (os th) = var zeroth
liftSubst vf (o' th) = punchInNManyVars 1 0 (vf th)

substitute'' : forall {m n d} -> Term m d -> Subst m n -> Term n d
substitute'' (var th) vf = vf th
substitute'' (app e s) vf = app (substitute'' e vf) (substitute'' s vf)
substitute'' (the S s) vf = the S (substitute'' s vf)
substitute'' (lam s) vf = lam (substitute'' s (liftSubst vf))
substitute'' [ e ] vf = [ substitute'' e vf ]

substitute' : forall {m n d} l -> Term (l +N m) d -> Subst m n -> Term (l +N n) d
substitute' l (var th) vf with 1≤th-part l th
... | inl thl = var (1≤th-leftPart _ thl)
... | inr thm = punchInNManyVars l zero (vf thm)
substitute' l (app e s) vf = app (substitute' l e vf) (substitute' l s vf)
substitute' l (the S s) vf = the S (substitute' l s vf)
substitute' l (lam s) vf = lam (substitute' (succ l) s vf)
substitute' l [ e ] vf = [ substitute' l e vf ]

substitute : forall {m d} l -> QTy -> Term (l +N succ m) d -> Term m chk -> Term (l +N m) d
substitute l T (var th) t with 1≤thToNat th ==Nat? l
... | yes _ = punchInNManyVars l zero (the T t)
... | no neq = var (punchOutN l th neq)
substitute l T (app e s) t = app (substitute l T e t) (substitute l T s t)
substitute l T (the S s) t = the S (substitute l T s t)
substitute l T (lam s) t = lam (substitute (succ l) T s t)
substitute l T [ e ] t = [ substitute l T e t ]

data _~~>_ {n} : forall {d} (t u : Term n d) -> Set where
  beta : forall S T s0 s1 -> app (the (S ~> T) (lam s0)) s1 ~~> the T (substitute zero S s0 s1)
  upsilon : forall S s -> [ the S s ] ~~> s

singleSubst : forall {m} -> Term m syn -> Subst (succ m) m
singleSubst e (os th) = e
singleSubst e (o' th) = var th

data _~~>'_ {n} : forall {d} (t u : Term n d) -> Set where
  beta' : forall S T s0 s1 ->
          app (the (S ~> T) (lam s0)) s1
          ~~>' the T (substitute' zero s0 (singleSubst (the S s1)))
  upsilon' : forall S s -> [ the S s ] ~~>' s

punchInNManyVarsTySyn :
  forall {m n l T e} {Dm : Ctx m} (Dn : Ctx n) (Dl : Ctx l) ->
  Dl +V Dm |- e ∈ T -> Dl +V Dn +V Dm |- punchInNManyVars n l e ∈ T
punchInNManyVarsTyChk :
  forall {m n l T s} {Dm : Ctx m} (Dn : Ctx n) (Dl : Ctx l) ->
  Dl +V Dm |- T ∋ s -> Dl +V Dn +V Dm |- T ∋ punchInNManyVars n l s

punchInNManyVarsTySyn {l = l} {e = var th} {Dm} Dn Dl var
  rewrite sym (1≤th-index-punchInNMany Dl Dn Dm th) = var
punchInNManyVarsTySyn Dn Dl (app et st) =
  app (punchInNManyVarsTySyn Dn Dl et) (punchInNManyVarsTyChk Dn Dl st)
punchInNManyVarsTySyn Dn Dl (the st) = the (punchInNManyVarsTyChk Dn Dl st)

punchInNManyVarsTyChk Dn Dl (lam {S = S} st) = lam (punchInNManyVarsTyChk Dn (S :: Dl) st)
punchInNManyVarsTyChk Dn Dl [ et ] = [ punchInNManyVarsTySyn Dn Dl et ]

SubstTy : forall {m n} -> Subst m n -> Ctx m -> Ctx n -> Set c
SubstTy {m} {n} vf Dm Dn = (th : 1 ≤th m) -> Dn |- vf th ∈ 1≤th-index th Dm

liftSubstTy : forall {m n Dm Dn} T (vf : Subst m n) ->
              SubstTy vf Dm Dn -> SubstTy (liftSubst vf) (T :: Dm) (T :: Dn)
liftSubstTy T vf vft (os th) = var
liftSubstTy T vf vft (o' th) = punchInNManyVarsTySyn (T :: nil) nil (vft th)

substituteTySyn'' :
  forall {m n S} {e : Term m syn}
  {Dm : Ctx m} {Dn : Ctx n} ->
  Dm |- e ∈ S -> (vf : Subst m n) -> SubstTy vf Dm Dn ->
  Dn |- substitute'' e vf ∈ S
substituteTyChk'' :
  forall {m n S} {s : Term m chk}
  {Dm : Ctx m} {Dn : Ctx n} ->
  Dm |- S ∋ s -> (vf : Subst m n) -> SubstTy vf Dm Dn ->
  Dn |- S ∋ substitute'' s vf

substituteTySyn'' (var {th = th}) vf vft = vft th
substituteTySyn'' (app et st) vf vft = app (substituteTySyn'' et vf vft) (substituteTyChk'' st vf vft)
substituteTySyn'' (the st) vf vft = the (substituteTyChk'' st vf vft)

substituteTyChk'' (lam st) vf vft = lam (substituteTyChk'' st (liftSubst vf) (liftSubstTy _ vf vft))
substituteTyChk'' [ et ] vf vft = [ substituteTySyn'' et vf vft ]

substituteTySyn :
  forall {l m S T} {e : Term (l +N succ m) syn} {t : Term m chk}
  {Dm : Ctx m} (Dl : Ctx l) ->
  Dl +V T :: Dm |- e ∈ S -> Dm |- T ∋ t ->
  Dl +V Dm |- substitute l T e t ∈ S
substituteTyChk :
  forall {l m S T} {Dm : Ctx m} (Dl : Ctx l)
  {s : Term (l +N succ m) chk} {t : Term m chk} ->
  Dl +V T :: Dm |- S ∋ s -> Dm |- T ∋ t ->
  Dl +V Dm |- S ∋ substitute l T s t

substituteTySyn {l = l} {T = T} {e = var th} {Dm = Dm} Dl var tt'
  with 1≤thToNat th ==Nat? l
... | yes eq rewrite 1≤th-index-punchInNMany Dl nil (T :: Dm) th
                   | 1≤th-index-+ th Dl T Dm eq =
  the (punchInNManyVarsTyChk Dl nil tt')
... | no neq rewrite sym (1≤th-index-punchOutN th neq Dl T Dm) = var
substituteTySyn Dl (app et st) tt' =
  app (substituteTySyn Dl et tt') (substituteTyChk Dl st tt')
substituteTySyn Dl (the st) tt' = the (substituteTyChk Dl st tt')

substituteTyChk Dl (lam {S = S} st) tt' = lam (substituteTyChk (S :: Dl) st tt')
substituteTyChk Dl [ et ] tt' = [ substituteTySyn Dl et tt' ]

sg≤0->G≤0 :
  forall {n d G sg} {t : Term n d} ->
  G |-[ sg ] t -> sg->rho sg ≤ e0 -> G ≤G replicateVec n e0
sg≤0->G≤0 {sg = sg} (var {th = th} sub) le = go th sub
  where
  go : forall {n G} th -> G ≤G varQCtx th (sg->rho sg) -> G ≤G replicateVec n e0
  go (os th) (le' :: sub) = ≤-trans le' le :: sub
  go (o' th) (le' :: sub) = le' :: go th sub
sg≤0->G≤0 (app split er sr) le =
  ≤G-trans split
           (≤G-trans (sg≤0->G≤0 er le +G-mono sg≤0->G≤0 sr le)
                     (≤G-reflexive (fst +G-identity _)))
sg≤0->G≤0 (the sr) le = sg≤0->G≤0 sr le
sg≤0->G≤0 (lam sr) le = tailVZip (sg≤0->G≤0 sr le)
sg≤0->G≤0 [ er ] le = sg≤0->G≤0 er le

punchInNManyVarsRes :
  forall {l n m d sg} {t : Term (l +N m) d} {Gm : QCtx m} {Gn} (Gl : QCtx l) ->
  Gn ≤G replicateVec n e0 -> Gl +V Gm |-[ sg ] t ->
  Gl +V Gn +V Gm |-[ sg ] punchInNManyVars n l t
punchInNManyVarsRes {l = l} {n} {m} {sg = sg} {Gm = Gm} {Gn} Gl subn (var {th = th} sub)
  rewrite VZip== (varQCtx-part l th (sg->rho sg))
  with 1≤th-part l th
... | inl thl = var a
  where
  a : Gl +V Gn +V Gm ≤G varQCtx (1≤th-leftPart (n +N m) thl) (sg->rho sg)
  a rewrite VZip== (varQCtx-leftPart {l} (n +N m) thl (sg->rho sg))
          | VZip== (replicateVec-+V n m e0)
    = takeVZip Gl (varQCtx thl (sg->rho sg)) sub
        +VZip subn
        +VZip dropVZip Gl (varQCtx thl (sg->rho sg)) sub
... | inr thm = var a
  where
  a : Gl +V Gn +V Gm ≤G varQCtx (1≤th-rightPart l (1≤th-rightPart n thm)) (sg->rho sg)
  a rewrite VZip== (varQCtx-rightPart l (1≤th-rightPart n thm) (sg->rho sg))
          | VZip== (varQCtx-rightPart n thm (sg->rho sg))
    = takeVZip Gl (replicateVec l e0) sub
        +VZip subn
        +VZip dropVZip Gl (replicateVec l e0) sub
punchInNManyVarsRes {l = l} {n} {m} {Gm = Gm} {Gn} Gl sub (app {Ge = Ge} {Gs} split er sr)
  rewrite sym (VZip== (takeDropVec== l Ge))
        | sym (VZip== (takeDropVec== l Gs))
  with takeVec l Ge | dropVec l Ge | takeVec l Gs | dropVec l Gs
... | Gel | Gem | Gsl | Gsm
  rewrite VZip== (vzip-+V _+_ Gel Gsl Gem Gsm)
  =
  app split' (punchInNManyVarsRes Gel (≤G-refl _) er) (punchInNManyVarsRes Gsl (≤G-refl _) sr)
  where
  split' : Gl +V Gn +V Gm ≤G (Gel +V replicateVec n e0 +V Gem) +G (Gsl +V replicateVec n e0 +V Gsm)
  split' rewrite VZip== (vzip-+V _+_ Gel Gsl (replicateVec n e0 +V Gem) (replicateVec n e0 +V Gsm))
               | VZip== (vzip-+V _+_ (replicateVec n e0) (replicateVec n e0) Gem Gsm)
               | VZip== (fst +G-identity (replicateVec n e0))
    = takeVZip Gl (Gel +G Gsl) split
        +VZip sub
        +VZip dropVZip Gl (Gel +G Gsl) split
punchInNManyVarsRes Gl sub (the sr) = the (punchInNManyVarsRes Gl sub sr)
punchInNManyVarsRes {sg = sg} Gl sub (lam sr) =
  lam (punchInNManyVarsRes (sg->rho sg :: Gl) sub sr)
punchInNManyVarsRes Gl sub [ er ] = [ punchInNManyVarsRes Gl sub er ]

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

  --record _|-*[_]_ {m n} (Gn : QCtx n) (sgf : 1 ≤th m -> Two) (vf : Subst m n)
  --                : Set _ where
  --  field
  --    sub : Gn ≤G (vmap sg->rho (1≤th-tabulate sgf)) 
  --    --res : 
  --Gn |-*[ sgf ] vf = {!Gn ≤G vmap sg->rho (1≤th-tabulate sgf)
  --                 × ((th : 1 ≤th m) -> ?)!}

  sumG : forall {m n} -> (1 ≤th m -> QCtx n) -> QCtx n
  sumG f =
    fold (replicateVec _ e0) _+G_ (fst (Vec->LengthedList (1≤th-tabulate f)))

  --SubstRes : forall {m n} (vf : Subst m n) -> QCtx m -> QCtx n -> Set _
  --SubstRes {m} {n} vf Gm Gn = {!!}
  --  --Sg (Vec Two m) \ Gsg ->
  --  --  (th : 1 ≤th m) -> let sg = 1≤th-index th Gsg in
  --  --                    varQCtx th (sg->rho sg) |-[ sg ] vf th
  record SubstRes {m n} (vf : Subst m n) (Gm : QCtx m) (Gn : QCtx n)
                  : Set (c ⊔ l') where
    field
      sgf : 1 ≤th m -> Two
      Gnf : 1 ≤th m -> QCtx n
      split : Gn ≤G sumG (\ th -> 1≤th-index th Gm *G Gnf th) --(\ th -> sg->rho (sgf th) *G Gnf th)
      resf : (th : 1 ≤th m) -> Gnf th |-[ sgf th ] vf th
      eqf : (th : 1 ≤th m) -> let rho = 1≤th-index th Gm in
                              sg->rho (sgf th) * rho == rho

  infix 3 _|-*[_,_]_

  data _|-*[_,_]_ {n d} (G : QCtx n)
                : forall {m} -> Vec Two m -> Vec C m -> Vec (Term n d) m ->
                  Set (c ⊔ l')
                where
    nil : (split : G ≤G replicateVec n e0) -> G |-*[ nil , nil ] nil
    cons : forall {m Gt Gts sg rho t sgs rhos} {ts : Vec _ m}
           (eq : sg->rho sg * rho == rho) (split : G ≤G rho *G Gt +G Gts)
           (tr : Gt |-[ sg ] t) (tsr : Gts |-*[ sgs , rhos ] ts) ->
           G |-*[ sg :: sgs , rho :: rhos ] t :: ts

  SubstRes' : forall {m n} -> Subst m n -> Vec Two m -> QCtx m -> QCtx n -> Set (c ⊔ l')
  SubstRes' {m} {n} vf sgs Gm Gn = Gn |-*[ sgs , Gm ] 1≤th-tabulate vf

  rho->sg : C -> Two
  rho->sg = not o floor o (_≤? e0)

  SubstRes'' : forall {m n} -> Subst m n -> QCtx m -> QCtx n -> Set (c ⊔ l')
  SubstRes'' {m} {n} vf Gm Gn =
    (th : 1 ≤th m) -> let sg = not (floor (1≤th-index th Gm ≤? e0)) in Gn |-[ sg ] vf th

  punchInNManyVarsRes* :
    forall {l n m o d sgs rhos} {ts : Vec (Term (l +N m) d) o}
    {Gm : QCtx m} {Gn} (Gl : QCtx l) ->
    Gn ≤G replicateVec n e0 -> Gl +V Gm |-*[ sgs , rhos ] ts ->
    Gl +V Gn +V Gm |-*[ sgs , rhos ] vmap (punchInNManyVars n l) ts
  punchInNManyVarsRes* {l} {n} {m} {Gm = Gm} {Gn} Gl sub (nil split) =
    nil split'
    where
    split' : Gl +V Gn +V Gm ≤G replicateVec (l +N n +N m) e0
    split' rewrite VZip== (replicateVec-+V l m e0)
                 | VZip== (replicateVec-+V l (n +N m) e0)
                 | VZip== (replicateVec-+V n m e0)
      = takeVZip Gl (replicateVec l e0) split
          +VZip sub
          +VZip dropVZip Gl (replicateVec l e0) split
  punchInNManyVarsRes* {l} {n} {sgs = sg :: sgs} {rho :: rhos} {t :: ts} {Gm}
                       {Gn} Gl sub (cons {Gt = Gt} {Gts} eq split tr tsr) =
    cons eq split'
         (punchInNManyVarsRes (takeVec l Gt) (≤G-refl _) tr')
         (punchInNManyVarsRes* (takeVec l Gts) sub tsr')
    where
    split' : Gl +V Gn +V Gm ≤G rho *G (takeVec l Gt +V replicateVec n e0 +V dropVec l Gt)
                                 +G (takeVec l Gts +V Gn +V dropVec l Gts)
    split' rewrite VZip== (vmap-+V (rho *_) (takeVec l Gt) (replicateVec n e0 +V dropVec l Gt))
                 | VZip== (vmap-+V (rho *_) (replicateVec n e0) (dropVec l Gt))
                 | VZip== (vzip-+V _+_ (rho *G takeVec l Gt)
                                       (takeVec l Gts)
                                       (rho *G replicateVec n e0 +V rho *G dropVec l Gt)
                                       (Gn +V dropVec l Gts))
                 | VZip== (vzip-+V _+_ (rho *G replicateVec n e0) Gn
                                       (rho *G dropVec l Gt) (dropVec l Gts))
                 | sym (VZip== (takeDropVec== l Gt))
                 | sym (VZip== (takeDropVec== l Gts))
                 | VZip== (vmap-+V (rho *_) (takeVec l Gt) (dropVec l Gt))
                 | VZip== (vzip-+V _+_ (rho *G takeVec l Gt) (takeVec l Gts)
                                       (rho *G dropVec l Gt) (dropVec l Gts))
                 | VZip== (takeDropVec== l Gt)
                 | VZip== (takeDropVec== l Gts)
      = takeVZip Gl (rho *G takeVec l Gt +G takeVec l Gts) split
          +VZip ≤G-reflexive (
            Gn
              ≈[ ≈G-sym (fst +G-identity Gn) ]G
            replicateVec n e0 +G Gn
              ≈[ ≈G-sym (*Gempty rho n +G-cong ≈G-refl Gn) ]G
            rho *G replicateVec n e0 +G Gn
              ≈G-QED
          )
          +VZip dropVZip Gl (rho *G takeVec l Gt +G takeVec l Gts) split

    --split' : Gl +V Gn +V Gm ≤G rho *G (takeVec l Gt +V Gn +V dropVec l Gt) +G (takeVec l Gts +V Gn +V dropVec l Gts)
    --split' rewrite VZip== (vmap-+V (rho *_) (takeVec l Gt) (Gn +V dropVec l Gt))
    --             | VZip== (vmap-+V (rho *_) Gn (dropVec l Gt))
    --             | VZip== (vzip-+V _+_ (rho *G takeVec l Gt) (takeVec l Gts) (rho *G Gn +V rho *G dropVec l Gt) (Gn +V dropVec l Gts))
    --             | VZip== (vzip-+V _+_ (rho *G Gn) Gn (rho *G dropVec l Gt) (dropVec l Gts))
    --             | sym (VZip== (takeDropVec== l Gt))
    --             | sym (VZip== (takeDropVec== l Gts))
    --             | VZip== (vmap-+V (rho *_) (takeVec l Gt) (dropVec l Gt))
    --             | VZip== (vzip-+V _+_ (rho *G takeVec l Gt) (takeVec l Gts) (rho *G dropVec l Gt) (dropVec l Gts))
    --             | VZip== (takeDropVec== l Gt)
    --             | VZip== (takeDropVec== l Gts)
    --  = takeVZip Gl (rho *G takeVec l Gt +G takeVec l Gts) split
    --      +VZip (
    --        Gn                    ≤[ {!!} ]G
    --        replicateVec n e0 +G Gn  ≤[ {!sub!} ]G
    --        rho *G Gn +G Gn       ≤G-QED
    --      )
    --      +VZip dropVZip Gl (rho *G takeVec l Gt +G takeVec l Gts) split

    tr' : takeVec l Gt +V dropVec l Gt |-[ sg ] t
    tr' rewrite VZip== (takeDropVec== l Gt) = tr

    tsr' : takeVec l Gts +V dropVec l Gts |-*[ sgs , rhos ] ts
    tsr' rewrite VZip== (takeDropVec== l Gts) = tsr

  liftSubstRes' : forall {m n sgs Gm Gn} sg (vf : Subst m n) ->
                  let rho = sg->rho sg in
                  SubstRes' vf sgs Gm Gn ->
                  SubstRes' (liftSubst vf) (sg :: sgs) (rho :: Gm) (rho :: Gn)
  liftSubstRes' {sgs = sgs} {Gm} {Gn} sg vf vfr =
    cons (sg*sg==sg sg) split (var (≤G-refl _)) vfr'
    where
    split : sg->rho sg :: Gn ≤G sg->rho sg *G (sg->rho sg :: replicateVec _ e0) +G (e0 :: Gn)
    split = ≤G-reflexive (sym (
        sg->rho sg * sg->rho sg + e0  =[ snd +-identity _ ]=
        sg->rho sg * sg->rho sg       =[ sg*sg==sg sg ]=
        sg->rho sg                    QED
      )
      :: ≈G-sym ((
        sg->rho sg *G replicateVec _ e0 +G Gn  ≈[ *Gempty _ _ +G-cong ≈G-refl Gn ]G
                      replicateVec _ e0 +G Gn  ≈[ fst +G-identity Gn ]G
                                        Gn  ≈G-QED
      )))

    vfr' : e0 :: Gn |-*[ sgs , Gm ] 1≤th-tabulate (punchInNManyVars 1 0 o vf)
    vfr' rewrite VZip== (1≤th-tabulate-o (punchInNManyVars 1 0) vf) =
      punchInNManyVarsRes* nil (≤-refl :: nil) vfr

  weakenRes* : forall {m n d G G'} {ts : Vec (Term n d) m} {sgs rhos} ->
               G' ≤G G -> G |-*[ sgs , rhos ] ts -> G' |-*[ sgs , rhos ] ts
  weakenRes* sub (nil split) = nil (≤G-trans sub split)
  weakenRes* sub (cons eq split tr tsr) = cons eq (≤G-trans sub split) tr tsr

  --substituteRes* :
  --  forall {m n o d sgs sgs' rhos} {ts : Vec (Term m d) o}
  --  {Gm : QCtx m} {Gn : QCtx n} ->
  --  vzip (\ sg' rho -> sg->rho sg' * rho) sgs' Gm ≈G Gm ->
  --  Gm |-*[ sgs , rhos ] ts -> (vf : Subst m n) -> SubstRes' vf sgs' Gm Gn ->
  --  Gn |-*[ sgs , rhos ] vmap (\ t -> substitute'' t vf) ts
  --substituteRes* eqs (nil split) vf vfr = nil {!split!}
  --substituteRes* eqs (cons eq split tr tsr) vf vfr = cons eq {!split!} {!vfr!} {!!}

  sg*Res :
    forall {n d G G' sg sg' rho} {t : Term n d} ->
    sg->rho sg' * rho ≤ sg->rho sg -> G ≤G rho *G G' -> G' |-[ sg' ] t -> G |-[ sg ] t
  sg*Res {G = G} {G'} {sg} {sg'} {rho} {var th} le sub (var sub') =
    var (
      G                                ≤[ sub ]G
      rho *G G'                        ≤[ ≤-refl *G-mono sub' ]G
      rho *G varQCtx th (sg->rho sg')  ≤[ {!!} ]G
      varQCtx th (rho * sg->rho sg')   ≤[ {!le!} ]G
      varQCtx th (sg->rho sg)          ≤G-QED
    )
  sg*Res le sub (app split er sr) = {!!}
  sg*Res le sub (the sr) = the (sg*Res le sub sr)
  sg*Res le sub (lam sr) = lam (sg*Res le ({!le!} :: sub) sr)
  sg*Res le sub [ er ] = [ sg*Res le sub er ]

  substituteRes' :
    forall {m n d sg sgs} {t : Term m d}
    {Gm : QCtx m} {Gn : QCtx n} ->
    vzip (\ sg' rho -> sg->rho sg' * rho) sgs Gm ≈G Gm ->
    Gm |-[ sg ] t -> (vf : Subst m n) -> SubstRes' vf sgs Gm Gn ->
    Gn |-[ sg ] substitute'' t vf
  substituteRes' {n = n} {sg = sg} {Gn = Gn} eqs (var {th = th} sub) vf vfr = go th sub vf vfr
    where
    go : forall {m sgs} {Gm : QCtx m} (th : 1 ≤th m) →
         Gm ≤G varQCtx th (sg->rho sg) → (vf : Subst m n) (vfr : Gn |-*[ sgs , Gm ] 1≤th-tabulate vf) →
         Gn |-[ sg ] vf th
    go {succ m} {sg' :: sgs} {rho :: Gm} (os {n = .m} th) (le :: sub) vf (cons {Gt = Gt} {Gts} eq split tr vfr) rewrite z≤th-unique (z≤th _) th =
      let split' =
                     Gn                 ≤[ split ]G
           rho *G Gt +G Gts             ≤[ ≤G-refl _ +G-mono {!sub!} ]G
           rho *G Gt +G replicateVec n e0  ≤[ ≤G-reflexive (snd +G-identity _) ]G
           rho *G Gt                    ≤G-QED
      in
      {!tr!}
    go {Gm = rho :: Gm} (o' th) (le :: sub) vf (cons {Gt = Gt} {Gts} eq split tr vfr) =
      let split' =
                          Gn      ≤[ split ]G
                rho *G Gt +G Gts  ≤[ le *G-mono ≤G-refl Gt +G-mono ≤G-refl Gts ]G
                 e0 *G Gt +G Gts  ≤[ ≤G-reflexive (e0*G Gt) +G-mono ≤G-refl Gts ]G
           replicateVec n e0 +G Gts  ≤[ ≤G-reflexive (fst +G-identity Gts) ]G
                             Gts  ≤G-QED
      in
      go th sub (vf o o') (weakenRes* split' vfr)
  substituteRes' eqs (app split er sr) vf vfr = {!split!}
  substituteRes' eqs (the sr) vf vfr = the (substituteRes' eqs sr vf vfr)
  substituteRes' {sg = sg} eqs (lam sr) vf vfr =
    lam (substituteRes' (sg*sg==sg sg :: eqs) sr (liftSubst vf) (liftSubstRes' sg vf vfr))
  substituteRes' eqs [ er ] vf vfr = [ substituteRes' eqs er vf vfr ]

  substituteRes :
    forall {l m d rho sg sg' T} {s : Term (l +N succ m) d} {t : Term m chk} ->
    {Gm Gt : QCtx m} (Gl : QCtx l) -> sg->rho sg' * rho == rho ->
    Gl +V rho :: Gm |-[ sg ] s -> Gt |-[ sg' ] t ->
    Gl +V (Gm +G rho *G Gt) |-[ sg ] substitute l T s t
  substituteRes {l = l} {m} {rho = rho} {sg} {t = t} {Gm = Gm} {Gt} Gl s'r=r (var {th = th} sub) tr
    with 1≤thToNat th ==Nat? l
  ... | yes eq rewrite VZip== (varQCtx-3parts l th (sg->rho sg) eq) =
    the (punchInNManyVarsRes {Gn = Gl} nil (takeVZip Gl (replicateVec l e0) sub) {!eq!})
    where
    w : forall {t : Term m chk} sg' -> rho *G Gt |-[ sg' ] t -> Gm +G rho *G Gt |-[ sg' ] t
    w sg' = weakenRes
      (Gm +G rho *G Gt
         ≤[ tailVZip (dropVZip Gl (replicateVec l e0) sub) +G-mono ≤G-refl (rho *G Gt) ]G
       replicateVec _ e0 +G rho *G Gt
         ≤[ ≤G-reflexive (fst +G-identity _) ]G
       rho *G Gt  ≤G-QED)

    tr' : forall {t : Term m chk} sg' -> rho ≤ sg->rho sg' -> Gt |-[ sg' ] t -> Gm +G rho *G Gt |-[ sg' ] t
    tr' tt le tr = w tt (weakenRes (rho *G Gt  ≤[ le *G-mono ≤G-refl Gt ]G
                                    e1 *G Gt   ≤[ ≤G-reflexive (fst *G-identity Gt) ]G
                                    Gt         ≤G-QED) tr)
    tr' ff le tr = w ff (weakenRes (rho *G Gt  ≤[ ≤-refl {rho} *G-mono sg≤0->G≤0 tr ≤-refl ]G
                                    rho *G replicateVec m e0  ≤[ {!!} ]G
                                    replicateVec m e0  ≤[ {!!} ]G
                                    Gt  ≤G-QED) tr)
  ... | no neq rewrite VZip== (varQCtx-part l th (sg->rho sg))
    with 1≤th-part l th | 1≤th-part-toNat l th
  ... | inl thl | eq = var {!punchOutN l th neq!}
  ... | inr (os thsm) | eq rewrite +N-zero l = Zero-elim (neq eq)
  ... | inr (o' thm) | eq = var {!!}
  substituteRes {l} {m} {rho = rho} {Gm = Gm} {Gt = Gt} Gl s'r=r (app {Ge = Ge} {Gs = Gs} split er sr) tr
    rewrite sym (VZip== (takeDropVec== l Ge))
          | sym (VZip== (takeDropVec== l Gs))
          | sym (VZip== (headTailVec== (dropVec l Ge)))
          | sym (VZip== (headTailVec== (dropVec l Gs)))
    with takeVec l Ge
       | takeVec l Gs
       | headVec (dropVec l Ge)
       | headVec (dropVec l Gs)
       | tailVec (dropVec l Ge)
       | tailVec (dropVec l Gs)
  ... | Gel | Gsl | rhoe | rhos | Gem | Gsm
    rewrite VZip== (vzip-+V _+_ Gel Gsl (rhoe :: Gem) (rhos :: Gsm))
    with tailVZip (dropVZip Gl (Gel +G Gsl) split)
         +G-mono headVZip (dropVZip Gl (Gel +G Gsl) split) *G-mono (≤G-refl Gt)
  ... | split'sm
  -- should all be a rewrite, but Agda doesn't like that  vvv
    with VZip==
         ((Gem +G Gsm) +G (rhoe + rhos) *G Gt         ≈[ ≈G-refl _ +G-cong *G-distrib-+ Gt rhoe rhos ]G
          (Gem +G Gsm) +G (rhoe *G Gt +G rhos *G Gt)  ≈[ +G-assoc Gem Gsm _ ]G
          Gem +G (Gsm +G (rhoe *G Gt +G rhos *G Gt))  ≈[ ≈G-refl _ +G-cong ≈G-sym (+G-assoc Gsm _ _) ]G
          Gem +G ((Gsm +G rhoe *G Gt) +G rhos *G Gt)  ≈[ ≈G-refl _ +G-cong (+G-comm Gsm _ +G-cong ≈G-refl _) ]G
          Gem +G ((rhoe *G Gt +G Gsm) +G rhos *G Gt)  ≈[ ≈G-refl _ +G-cong +G-assoc _ Gsm _ ]G
          Gem +G (rhoe *G Gt +G (Gsm +G rhos *G Gt))  ≈[ ≈G-sym (+G-assoc Gem _ _) ]G
          (Gem +G rhoe *G Gt) +G (Gsm +G rhos *G Gt)  ≈G-QED)
  ... | eq
    with (Gem +G Gsm) +G (rhoe + rhos) *G Gt
  ... | zzz with eq
  ... | refl
    with _+VZip_ (takeVZip Gl (Gel +G Gsl) split) split'sm
  ... | split'
    rewrite sym (VZip== (vzip-+V _+_ Gel Gsl (Gem +G rhoe *G Gt) (Gsm +G rhos *G Gt)))
    =
    app split' (substituteRes Gel {!!} er tr) (substituteRes Gsl {!!} sr tr)
  substituteRes Gl s'r=r (the sr) tr = the (substituteRes Gl s'r=r sr tr)
  substituteRes {sg = sg} Gl s'r=r (lam sr) tr =
    lam (substituteRes (sg->rho sg :: Gl) s'r=r sr tr)
  substituteRes Gl s'r=r [ er ] tr = [ substituteRes Gl s'r=r er tr ]

  {-+}
  ~~>-preserves-res : forall {n d G sg} {t u : Term n d} {tr : G |-[ sg ] t} ->
                      t ~~> u -> G |-[ sg ] u
  ~~>-preserves-res {t = .(app (the (S ~> T) (lam s0)) s1)} {.(the T (substitute (os (z≤th _)) S s0 s1))} {app split (the (lam s0r)) s1r} (beta S T s0 s1) = the (substitute-res split s0r s1r)
  ~~>-preserves-res {t = .([ the S s ])} {.s} {[ the tr ]} (upsilon S s) = tr
  {+-}
