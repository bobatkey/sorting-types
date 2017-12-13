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

0G : forall {n} -> QCtx n
0G = replicateVec _ e0

varQCtx : forall {n} -> 1 ≤th n -> C -> QCtx n
varQCtx (os th) rho = rho :: 0G
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

varQCtx-e0 : forall {n} (i : 1 ≤th n) -> varQCtx i e0 ≈G 0G
varQCtx-e0 (os i) = ≈G-refl _
varQCtx-e0 (o' i) = refl :: varQCtx-e0 i

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
  forall {n} i rho (G : QCtx n) ->
  1≤th-insertVec i rho G ≤G varQCtx i rho -> G ≤G 0G
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
    { (inl thl) -> varQCtx thl rho +V 0G
    ; (inr thm) -> 0G {l} +V varQCtx thm rho
    }
varQCtx-part zero th rho = ≈G-refl _
varQCtx-part (succ l) (os th) rho = refl :: replicateVec-+V l _ e0
varQCtx-part (succ l) (o' th) rho with 1≤th-part l th | varQCtx-part l th rho
varQCtx-part (succ l) (o' th) rho | inl thl | r = refl :: r
varQCtx-part (succ l) (o' th) rho | inr thm | r = refl :: r

varQCtx-leftPart :
  forall {m} n (th : 1 ≤th m) rho ->
  varQCtx (1≤th-leftPart n th) rho ≈G varQCtx th rho +V 0G
varQCtx-leftPart {succ m} n (os th) rho = refl :: replicateVec-+V m n e0
varQCtx-leftPart {succ m} n (o' th) rho = refl :: varQCtx-leftPart n th rho

varQCtx-rightPart :
  forall m {n} (th : 1 ≤th n) rho ->
  varQCtx (1≤th-rightPart m th) rho ≈G 0G {m} +V varQCtx th rho
varQCtx-rightPart zero th rho = ≈G-refl _
varQCtx-rightPart (succ m) th rho = refl :: varQCtx-rightPart m th rho

varQCtx-3parts :
  forall m {n} (th : 1 ≤th m +N succ n) rho -> 1≤thToNat th == m ->
  varQCtx th rho ≈G 0G {m} +V rho :: 0G
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

+G-identity : (forall {n} G -> 0G {n} +G G ≈G G)
            × (forall {n} G -> G +G 0G {n} ≈G G)
fst +G-identity = go
  where
  go : forall {n} G -> 0G {n} +G G ≈G G
  go nil = nil
  go (p :: G) = fst +-identity p :: go G
snd +G-identity = go
  where
  go : forall {n} G -> G +G 0G {n} ≈G G
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
*G-distrib-+ (p :: G) rho rho' =
  snd distrib p rho rho' :: *G-distrib-+ G rho rho'

*G-distrib-+G : forall {n} (rho : C) (G G' : QCtx n) ->
                rho *G (G +G G') ≈G rho *G G +G rho *G G'
*G-distrib-+G rho nil nil = nil
*G-distrib-+G rho (p :: G) (p' :: G') =
  fst distrib rho p p' :: *G-distrib-+G rho G G'

e0*G : forall {n} G -> e0 *G G ≈G 0G {n}
e0*G nil = nil
e0*G (p :: G) = fst annihil p :: e0*G G

*Gempty : forall {n} rho -> rho *G 0G ≈G 0G {n}
*Gempty rho =
  rho *G replicateVec _ e0   ≈[ vmap-replicateVec (rho *_) _ e0 ]G
  replicateVec _ (rho * e0)  ≈[ replicateVZip _ (snd annihil rho) ]G
  replicateVec _ e0          ≈G-QED

*GvarQCtx : forall {n} rho (i : 1 ≤th n) rho' ->
            rho *G varQCtx i rho' ≈G varQCtx i (rho * rho')
*GvarQCtx rho (os i) rho' = refl :: *Gempty rho
*GvarQCtx rho (o' i) rho' = snd annihil rho :: *GvarQCtx rho i rho'

varQCtx-≤ : forall {n rho rho'} (i : 1 ≤th n) -> rho ≤ rho' ->
            varQCtx i rho ≤G varQCtx i rho'
varQCtx-≤ (os i) le = le :: ≤G-refl _
varQCtx-≤ (o' i) le = ≤-refl :: varQCtx-≤ i le

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

substitute : forall {m n d} -> Term m d -> Subst m n -> Term n d
substitute (var th) vf = vf th
substitute (app e s) vf = app (substitute e vf) (substitute s vf)
substitute (the S s) vf = the S (substitute s vf)
substitute (lam s) vf = lam (substitute s (liftSubst vf))
substitute [ e ] vf = [ substitute e vf ]

singleSubst : forall {m} -> Term m syn -> Subst (succ m) m
singleSubst e (os th) = e
singleSubst e (o' th) = var th

data _~~>_ {n} : forall {d} (t u : Term n d) -> Set where
  beta : forall S T s0 s1 ->
          app (the (S ~> T) (lam s0)) s1
          ~~> the T (substitute s0 (singleSubst (the S s1)))
  upsilon : forall S s -> [ the S s ] ~~> s
  lam-cong : forall s0 s1 -> s0 ~~> s1 -> lam s0 ~~> lam s1
  app1-cong : forall e0 e1 s -> e0 ~~> e1 -> app e0 s ~~> app e1 s
  app2-cong : forall e s0 s1 -> s0 ~~> s1 -> app e s0 ~~> app e s1

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

singleSubstTy : forall {m D e S} -> D |- e ∈ S -> SubstTy (singleSubst {m} e) (S :: D) D
singleSubstTy et (os th) = et
singleSubstTy et (o' th) = var

liftSubstTy : forall {m n Dm Dn} T (vf : Subst m n) ->
              SubstTy vf Dm Dn -> SubstTy (liftSubst vf) (T :: Dm) (T :: Dn)
liftSubstTy T vf vft (os th) = var
liftSubstTy T vf vft (o' th) = punchInNManyVarsTySyn (T :: nil) nil (vft th)

substituteTySyn :
  forall {m n S} {e : Term m syn}
  {Dm : Ctx m} {Dn : Ctx n} ->
  Dm |- e ∈ S -> (vf : Subst m n) -> SubstTy vf Dm Dn ->
  Dn |- substitute e vf ∈ S
substituteTyChk :
  forall {m n S} {s : Term m chk}
  {Dm : Ctx m} {Dn : Ctx n} ->
  Dm |- S ∋ s -> (vf : Subst m n) -> SubstTy vf Dm Dn ->
  Dn |- S ∋ substitute s vf

substituteTySyn (var {th = th}) vf vft = vft th
substituteTySyn (app et st) vf vft = app (substituteTySyn et vf vft) (substituteTyChk st vf vft)
substituteTySyn (the st) vf vft = the (substituteTyChk st vf vft)

substituteTyChk (lam st) vf vft = lam (substituteTyChk st (liftSubst vf) (liftSubstTy _ vf vft))
substituteTyChk [ et ] vf vft = [ substituteTySyn et vf vft ]

~~>-preservesTySyn : forall {n D T} {e f : Term n syn} (et : D |- e ∈ T) ->
                     e ~~> f -> D |- f ∈ T
~~>-preservesTyChk : forall {n D T} {s t : Term n chk} (st : D |- T ∋ s) ->
                     s ~~> t -> D |- T ∋ t

~~>-preservesTySyn (app (the (lam s0t)) s1t) (beta S T s0 s1) =
  the (substituteTyChk s0t (singleSubst (the S s1)) (singleSubstTy (the s1t)))
~~>-preservesTySyn (app et st) (app1-cong e0 e1 s red) = app (~~>-preservesTySyn et red) st
~~>-preservesTySyn (app et st) (app2-cong e s0 s1 red) = app et (~~>-preservesTyChk st red)

~~>-preservesTyChk [ the st ] (upsilon S s) = st
~~>-preservesTyChk (lam s0t) (lam-cong s0 s1 red) = lam (~~>-preservesTyChk s0t red)

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
  split' : Gl +V Gn +V Gm ≤G (Gel +V 0G {n} +V Gem) +G (Gsl +V 0G {n} +V Gsm)
  split' rewrite VZip== (vzip-+V _+_ Gel Gsl (0G {n} +V Gem) (0G {n} +V Gsm))
               | VZip== (vzip-+V _+_ (0G {n}) (0G {n}) Gem Gsm)
               | VZip== (fst +G-identity (0G {n}))
    = takeVZip Gl (Gel +G Gsl) split
        +VZip sub
        +VZip dropVZip Gl (Gel +G Gsl) split
punchInNManyVarsRes Gl sub (the sr) = the (punchInNManyVarsRes Gl sub sr)
punchInNManyVarsRes {sg = sg} Gl sub (lam sr) =
  lam (punchInNManyVarsRes (sg->rho sg :: Gl) sub sr)
punchInNManyVarsRes Gl sub [ er ] = [ punchInNManyVarsRes Gl sub er ]

zeroRes : forall {n d G} {t : Term n d} {sg} ->
          G |-[ sg ] t -> 0G |-[ ff ] t
zeroRes (var {th} sub) = var (≤G-reflexive (≈G-sym (varQCtx-e0 th)))
zeroRes (app split er sr) =
  app (≤G-reflexive (≈G-sym (fst +G-identity _))) (zeroRes er) (zeroRes sr)
zeroRes (the sr) = the (zeroRes sr)
zeroRes (lam sr) = lam (zeroRes sr)
zeroRes [ er ] = [ zeroRes er ]

-- just in case e1 == e0, which seems a bit silly but is possible
==zeroRes : forall {n d G} {t : Term n d} {sg sg'} -> sg->rho sg' == e0 ->
            G |-[ sg ] t -> 0G |-[ sg' ] t
==zeroRes {sg' = sg'} eq (var {th} sub) = var sub'
  where
  sub' : 0G ≤G varQCtx th (sg->rho sg')
  sub' rewrite eq = ≤G-reflexive (≈G-sym (varQCtx-e0 th))
==zeroRes eq (app split er sr) =
  app (≤G-reflexive (≈G-sym (fst +G-identity _)))
      (==zeroRes eq er)
      (==zeroRes eq sr)
==zeroRes eq (the sr) = the (==zeroRes eq sr)
==zeroRes {t = lam s} {sg' = sg'} eq (lam sr) = lam sr'
  where
  sr' : sg->rho sg' :: 0G |-[ sg' ] s
  sr' rewrite eq = ==zeroRes eq sr
==zeroRes eq [ er ] = [ ==zeroRes eq er ]

resWasZero : forall {n d G} {t : Term n d} -> G |-[ ff ] t -> G ≤G 0G
resWasZero (var {th} sub) = ≤G-trans sub (≤G-reflexive (varQCtx-e0 th))
resWasZero {G = G} (app {Ge = Ge} {Gs} split er sr) =
      G     ≤[ split ]G
  Ge +G Gs  ≤[ resWasZero er +G-mono resWasZero sr ]G
  0G +G 0G  ≤[ ≤G-reflexive (fst +G-identity 0G) ]G
        0G  ≤G-QED
resWasZero (the sr) = resWasZero sr
resWasZero (lam sr) = tailVZip (resWasZero sr)
resWasZero [ er ] = resWasZero er

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

  infix 3 _|-*[_,_]_

  data _|-*[_,_]_ {n d} (G : QCtx n)
                : forall {m} -> Vec Two m -> Vec C m -> Vec (Term n d) m ->
                  Set (c ⊔ l')
                where
    nil : (split : G ≤G 0G) -> G |-*[ nil , nil ] nil
    cons : forall {m Gt Gts sg rho t sgs rhos} {ts : Vec _ m}
           (eq : sg->rho sg * rho == rho) (split : G ≤G rho *G Gt +G Gts)
           (tr : Gt |-[ sg ] t) (tsr : Gts |-*[ sgs , rhos ] ts) ->
           G |-*[ sg :: sgs , rho :: rhos ] t :: ts

  lift|-*[,] : forall {m n G sgs rhos} {vf : Subst m n} ->
               G |-*[ sgs , rhos ] 1≤th-tabulate vf -> e0 :: G |-*[ sgs , rhos ] 1≤th-tabulate (punchInNManyVars 1 0 o vf)
  lift|-*[,] (nil split) = nil (≤-refl :: split)
  lift|-*[,] (cons eq split tr tsr) =
    cons eq (≤-reflexive (sym (trans (snd +-identity _) (snd annihil _))) :: split)
            (punchInNManyVarsRes nil (≤G-refl _) tr)
            (lift|-*[,] tsr)

  |-*[,]-id : forall {n} (G : QCtx n) ->
              G |-*[ replicateVec n tt , G ] 1≤th-tabulate var
  |-*[,]-id nil = nil nil
  |-*[,]-id (rho :: G) =
    cons (fst *-identity rho)
         (≤G-reflexive (≈G-sym (≈G-trans
           (snd +-identity _   :: *Gempty rho +G-cong ≈G-refl G)
           (snd *-identity rho :: fst +G-identity G))))
         (var (≤G-refl _))
         (lift|-*[,] (|-*[,]-id G))

  SubstRes : forall {m n} -> Subst m n -> Vec Two m -> QCtx m -> QCtx n -> Set (c ⊔ l')
  SubstRes {m} {n} vf sgs Gm Gn = Gn |-*[ sgs , Gm ] 1≤th-tabulate vf

  singleSubstRes : forall {m G G0 G1 sg t} -> G0 |-[ sg ] t -> G ≤G sg->rho sg *G G0 +G G1 ->
                   SubstRes (singleSubst t) (sg :: replicateVec m tt) (sg->rho sg :: G1) G
  singleSubstRes {sg = sg} tr split = cons (sg*sg==sg sg) split tr (|-*[,]-id _)

  punchInNManyVarsRes* :
    forall {l n m o d sgs rhos} {ts : Vec (Term (l +N m) d) o}
    {Gm : QCtx m} {Gn} (Gl : QCtx l) ->
    Gn ≤G 0G {n} -> Gl +V Gm |-*[ sgs , rhos ] ts ->
    Gl +V Gn +V Gm |-*[ sgs , rhos ] vmap (punchInNManyVars n l) ts
  punchInNManyVarsRes* {l} {n} {m} {Gm = Gm} {Gn} Gl sub (nil split) =
    nil split'
    where
    split' : Gl +V Gn +V Gm ≤G 0G
    split' rewrite VZip== (replicateVec-+V l m e0)
                 | VZip== (replicateVec-+V l (n +N m) e0)
                 | VZip== (replicateVec-+V n m e0)
      = takeVZip Gl 0G split
          +VZip sub
          +VZip dropVZip Gl 0G split
  punchInNManyVarsRes* {l} {n} {sgs = sg :: sgs} {rho :: rhos} {t :: ts} {Gm}
                       {Gn} Gl sub (cons {Gt = Gt} {Gts} eq split tr tsr) =
    cons eq split'
         (punchInNManyVarsRes (takeVec l Gt) (≤G-refl _) tr')
         (punchInNManyVarsRes* (takeVec l Gts) sub tsr')
    where
    split' : Gl +V Gn +V Gm ≤G rho *G (takeVec l Gt +V 0G {n} +V dropVec l Gt)
                                 +G (takeVec l Gts +V Gn +V dropVec l Gts)
    split' rewrite VZip== (vmap-+V (rho *_) (takeVec l Gt) (0G {n} +V dropVec l Gt))
                 | VZip== (vmap-+V (rho *_) (0G {n}) (dropVec l Gt))
                 | VZip== (vzip-+V _+_ (rho *G takeVec l Gt)
                                       (takeVec l Gts)
                                       (rho *G 0G {n} +V rho *G dropVec l Gt)
                                       (Gn +V dropVec l Gts))
                 | VZip== (vzip-+V _+_ (rho *G 0G) Gn
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
            0G +G Gn
              ≈[ ≈G-sym (*Gempty rho +G-cong ≈G-refl Gn) ]G
            rho *G 0G +G Gn
              ≈G-QED
          )
          +VZip dropVZip Gl (rho *G takeVec l Gt +G takeVec l Gts) split

    tr' : takeVec l Gt +V dropVec l Gt |-[ sg ] t
    tr' rewrite VZip== (takeDropVec== l Gt) = tr

    tsr' : takeVec l Gts +V dropVec l Gts |-*[ sgs , rhos ] ts
    tsr' rewrite VZip== (takeDropVec== l Gts) = tsr

  from0G :
    forall {m n d sgs Gm Gn} {ts : Vec (Term n d) m} ->
    Gm ≤G 0G -> Gn |-*[ sgs , Gm ] ts -> Gn ≤G 0G
  from0G nil (nil split) = split
  from0G {Gm = Gm} {Gn} (le :: sub) (cons {Gt = Gt} {Gts} {rho = rho} eq split tr tsr) =
              Gn      ≤[ split ]G
    rho *G Gt +G Gts  ≤[ le *G-mono ≤G-refl Gt +G-mono ≤G-refl Gts ]G
     e0 *G Gt +G Gts  ≤[ ≤G-reflexive (e0*G Gt) +G-mono ≤G-refl Gts ]G
        0G    +G Gts  ≤[ ≤G-reflexive (fst +G-identity Gts) ]G
                 Gts  ≤[ from0G sub tsr ]G
                 0G   ≤G-QED

  liftSubstRes : forall {m n sgs Gm Gn} sg (vf : Subst m n) ->
                  let rho = sg->rho sg in
                  SubstRes vf sgs Gm Gn ->
                  SubstRes (liftSubst vf) (sg :: sgs) (rho :: Gm) (rho :: Gn)
  liftSubstRes {sgs = sgs} {Gm} {Gn} sg vf vfr =
    cons (sg*sg==sg sg) split (var (≤G-refl _)) vfr'
    where
    split : sg->rho sg :: Gn ≤G sg->rho sg *G (sg->rho sg :: 0G) +G (e0 :: Gn)
    split = ≤G-reflexive (sym (
        sg->rho sg * sg->rho sg + e0  =[ snd +-identity _ ]=
        sg->rho sg * sg->rho sg       =[ sg*sg==sg sg ]=
        sg->rho sg                    QED
      )
      :: ≈G-sym ((
        sg->rho sg *G 0G +G Gn  ≈[ *Gempty _ +G-cong ≈G-refl Gn ]G
                      0G +G Gn  ≈[ fst +G-identity Gn ]G
                                        Gn  ≈G-QED
      )))

    vfr' : e0 :: Gn |-*[ sgs , Gm ] 1≤th-tabulate (punchInNManyVars 1 0 o vf)
    vfr' rewrite VZip== (1≤th-tabulate-o (punchInNManyVars 1 0) vf) =
      punchInNManyVarsRes* nil (≤-refl :: nil) vfr

  weakenRes* : forall {m n d G G'} {ts : Vec (Term n d) m} {sgs rhos} ->
               G' ≤G G -> G |-*[ sgs , rhos ] ts -> G' |-*[ sgs , rhos ] ts
  weakenRes* sub (nil split) = nil (≤G-trans sub split)
  weakenRes* sub (cons eq split tr tsr) = cons eq (≤G-trans sub split) tr tsr

  nothingLeft :
    forall {m n d G sgs rhos} {ts : Vec (Term m d) n} ->
    rhos ≤G 0G -> G |-*[ sgs , rhos ] ts -> G ≤G 0G
  nothingLeft sub (nil split) = split
  nothingLeft {G = G} {rhos = rho :: rhos} (le :: sub) (cons {Gt = Gt} {Gts} eq split tr tsr) =
              G       ≤[ split ]G
    rho *G Gt +G Gts  ≤[ le *G-mono ≤G-refl Gt +G-mono nothingLeft sub tsr ]G
     e0 *G Gt +G 0G   ≤[ ≤G-reflexive (snd +G-identity _) ]G
     e0 *G Gt         ≤[ ≤G-reflexive (e0*G Gt) ]G
        0G            ≤G-QED

  substSplit : forall {m n vf sgs} {Gm Gem Gsm : QCtx m} {Gn : QCtx n} ->
               Gm ≤G Gem +G Gsm -> SubstRes vf sgs Gm Gn ->
               Sg _ \ Gen -> Sg _ \ Gsn -> Gn ≤G Gen +G Gsn
  substSplit {Gm = nil} {nil} {nil} {Gn} nil (nil split) =
    0G , 0G , ≤G-trans split (≤G-reflexive (≈G-sym (fst +G-identity 0G)))
  substSplit {Gm = rho :: Gm} {rhoe :: Gem} {rhos :: Gsm} {Gn} (le :: splitm) (cons {Gt = Gt} {Gts} eq splitn tr vfr)
    with substSplit splitm vfr
  ... | Gen , Gsn , split' =
    rhoe *G Gt +G Gen , rhos *G Gt +G Gsn ,
      Gn ≤[ splitn ]G
                 rho      *G Gt  +G     Gts       ≤[ le *G-mono ≤G-refl Gt +G-mono split' ]G
            (rhoe + rhos) *G Gt  +G (Gen +G Gsn)  ≤[ ≤G-reflexive equality ]G
      (rhoe *G Gt +G Gen) +G (rhos *G Gt +G Gsn)  ≤G-QED
    where
    equality : _
    equality =
            (rhoe + rhos) *G Gt  +G (Gen +G Gsn)  ≈[ *G-distrib-+ Gt rhoe rhos +G-cong ≈G-refl _ ]G
      (rhoe *G Gt +G rhos *G Gt) +G (Gen +G Gsn)  ≈[ +G-assoc _ _ _ ]G
      rhoe *G Gt +G (rhos *G Gt +G (Gen +G Gsn))  ≈[ ≈G-refl _ +G-cong ≈G-sym (+G-assoc _ _ _) ]G
      rhoe *G Gt +G ((rhos *G Gt +G Gen) +G Gsn)  ≈[ ≈G-refl _ +G-cong (+G-comm _ _ +G-cong ≈G-refl _) ]G
      rhoe *G Gt +G ((Gen +G rhos *G Gt) +G Gsn)  ≈[ ≈G-refl _ +G-cong +G-assoc _ _ _ ]G
      rhoe *G Gt +G (Gen +G (rhos *G Gt +G Gsn))  ≈[ ≈G-sym (+G-assoc _ _ _) ]G
      (rhoe *G Gt +G Gen) +G (rhos *G Gt +G Gsn)  ≈G-QED

  module ZeroMaximal (e0-maximal : forall {a} -> e0 ≤ a -> a == e0)
                     (positive : forall {a b} -> a + b == e0 -> a == e0 × b == e0)
                     where
    splitEq : forall {rho rho0 rho1 sg} ->
              rho ≤ rho0 + rho1 -> sg->rho sg * rho == rho ->
              sg->rho sg * rho0 == rho0 × sg->rho sg * rho1 == rho1
    splitEq {sg = tt} le eq = fst *-identity _ , fst *-identity _
    splitEq {rho} {rho0} {rho1} {sg = ff} le eq
      rewrite trans (sym eq) (fst annihil rho)
            | fst annihil rho0 | fst annihil rho1
      = mapSg sym sym (positive (e0-maximal le))

    splitEqs : forall {n G G0 G1 sgs} ->
               let f = vzip (\ sg rho -> sg->rho sg * rho) {n} in
               G ≤G G0 +G G1 -> f sgs G ≈G G ->
               f sgs G0 ≈G G0 × f sgs G1 ≈G G1
    splitEqs {G = nil} {nil} {nil} {nil} nil nil = nil , nil
    splitEqs {G = rho :: G} {rho0 :: G0} {rho1 :: G1} {sg :: sgs} (le :: split) (eq :: eqs)
      with splitEq {sg = sg} le eq | splitEqs split eqs
    ... | eq0 , eq1 | eqs0 , eqs1 =
      eq0 :: eqs0 , eq1 :: eqs1

    splitSubst : forall {m n vf sgs} {Gm Gem Gsm : QCtx m} {Gn : QCtx n}
                 (splitm : Gm ≤G Gem +G Gsm) (vfr : SubstRes vf sgs Gm Gn) ->
                 let Gen , Gsn , splitn = substSplit splitm vfr in
                 SubstRes vf sgs Gem Gen × SubstRes vf sgs Gsm Gsn
    splitSubst {Gm = nil} {nil} {nil} {Gn} nil (nil split) =
      nil (≤G-refl 0G) , nil (≤G-refl 0G)
    splitSubst {sgs = sg :: sgs} {Gm = rho :: Gm} {rhoe :: Gem} {rhos :: Gsm} {Gn} (le :: splitm) (cons eq split tr vfr)
      with splitSubst splitm vfr | splitEq {sg = sg} le eq
    ... | vfre , vfrs | eqe , eqs = cons eqe (≤G-refl _) tr vfre , cons eqs (≤G-refl _) tr vfrs

    substituteRes :
      forall {m n d sg sgs} {t : Term m d}
      {Gm : QCtx m} {Gn : QCtx n} ->
      vzip (\ sg' rho -> sg->rho sg' * rho) sgs Gm ≈G Gm ->
      Gm |-[ sg ] t -> (vf : Subst m n) -> SubstRes vf sgs Gm Gn ->
      Gn |-[ sg ] substitute t vf
    substituteRes {n = n} {sg = sg} {Gn = Gn} eqs (var {th = th} sub) vf vfr = go th sub vf vfr
      where
      go : forall {m sg sgs} {Gm : QCtx m} (th : 1 ≤th m) →
           Gm ≤G varQCtx th (sg->rho sg) → (vf : Subst m n) (vfr : Gn |-*[ sgs , Gm ] 1≤th-tabulate vf) →
           Gn |-[ sg ] vf th
      go {succ m} {sg} {sg' :: sgs} {rho :: Gm} (os {n = .m} th) (le :: sub) vf (cons {Gt = Gt} {Gts} eq split tr vfr) rewrite z≤th-unique (z≤th _) th with sg'
      go {succ m} {tt} {sg' :: sgs} {rho :: Gm} (os {_} {.m} th) (le :: sub) vf (cons {Gt = Gt} {Gts} eq split tr vfr) | tt =
        let split' =
                       Gn      ≤[ split ]G
             rho *G Gt +G Gts  ≤[ ≤G-refl _ +G-mono nothingLeft sub vfr ]G
             rho *G Gt +G 0G   ≤[ ≤G-reflexive (snd +G-identity _) ]G
             rho *G Gt         ≤[ le *G-mono ≤G-refl Gt ]G
              e1 *G Gt         ≤[ ≤G-reflexive (fst *G-identity Gt) ]G
                    Gt         ≤G-QED
        in
        weakenRes split' tr
      go {succ m} {ff} {sg' :: sgs} {rho :: Gm} (os {_} {.m} th) (le :: sub) vf (cons {Gt = Gt} {Gts} eq split tr vfr) | tt =
        let split' =
                       Gn      ≤[ split ]G
             rho *G Gt +G Gts  ≤[ le *G-mono ≤G-refl Gt +G-mono ≤G-refl Gts ]G
              e0 *G Gt +G Gts  ≤[ ≤G-reflexive (e0*G Gt) +G-mono ≤G-refl Gts ]G
                 0G    +G Gts  ≤[ ≤G-reflexive (fst +G-identity Gts) ]G
                          Gts  ≤[ from0G sub vfr ]G
                          0G   ≤G-QED
        in
        weakenRes split' (zeroRes tr)
      go {succ m} {sg} {sg' :: sgs} {rho :: Gm} (os {_} {.m} th) (le :: sub) vf (cons {Gt = Gt} {Gts} eq split tr vfr) | ff rewrite trans (sym eq) (fst annihil rho) =
        let split' =
                      Gn      ≤[ split ]G
             e0 *G Gt +G Gts  ≤[ ≤G-reflexive (e0*G Gt) +G-mono from0G sub vfr ]G
                0G    +G 0G   ≤[ ≤G-reflexive (fst +G-identity _) ]G
                         0G   ≤G-QED
        in
        weakenRes split' (==zeroRes {sg' = sg} (e0-maximal le) tr)
      go {Gm = rho :: Gm} (o' th) (le :: sub) vf (cons {Gt = Gt} {Gts} eq split tr vfr) =
        let split' =
                       Gn      ≤[ split ]G
             rho *G Gt +G Gts  ≤[ le *G-mono ≤G-refl Gt +G-mono ≤G-refl Gts ]G
              e0 *G Gt +G Gts  ≤[ ≤G-reflexive (e0*G Gt) +G-mono ≤G-refl Gts ]G
                 0G    +G Gts  ≤[ ≤G-reflexive (fst +G-identity Gts) ]G
                          Gts  ≤G-QED
        in
        go th sub (vf o o') (weakenRes* split' vfr)
    substituteRes {sgs = sgs} eqs (app split er sr) vf vfr
      with substSplit split vfr | splitSubst split vfr | splitEqs split eqs
    ... | Gen , Gsn , split' | vfre , vfrs | eqse , eqss =
      app split' (substituteRes eqse er vf vfre) (substituteRes eqss sr vf vfrs)
    substituteRes eqs (the sr) vf vfr = the (substituteRes eqs sr vf vfr)
    substituteRes {sg = sg} eqs (lam sr) vf vfr =
      lam (substituteRes (sg*sg==sg sg :: eqs) sr (liftSubst vf) (liftSubstRes sg vf vfr))
    substituteRes eqs [ er ] vf vfr = [ substituteRes eqs er vf vfr ]

    ~~>-preservesRes : forall {n d G sg} {t u : Term n d} (tr : G |-[ sg ] t) ->
                       t ~~> u -> G |-[ sg ] u
    ~~>-preservesRes {G = G} {sg} (app {Ge = Ge} {Gs} split (the (lam s0r)) s1r) (beta S T s0 s1) =
      the (substituteRes {sgs = sg :: replicateVec _ tt} (sg*sg==sg sg :: ≈G-trans (vzip-replicateVec (\ sg' rho -> sg->rho sg' * rho) _ tt Ge) (≈G-trans (vmap-funext (e1 *_) id Ge (fst *-identity)) (vmap-id Ge))) s0r _ (singleSubstRes (the {S = S} s1r) (split' sg s1r)))
      where
      split-eqs : Ge +G Gs ≈G sg->rho tt *G Gs +G Ge
      split-eqs =
              Ge +G Gs  ≈[ +G-comm Ge Gs ]G
              Gs +G Ge  ≈[ ≈G-sym (fst *G-identity Gs) +G-cong ≈G-refl Ge ]G
        e1 *G Gs +G Ge  ≈G-QED

      split' : forall {s1} sg -> Gs |-[ sg ] s1 -> G ≤G sg->rho sg *G Gs +G Ge
      split' tt s1r = ≤G-trans split (≤G-reflexive split-eqs)
      split' ff s1r =
                  G     ≤[ split ]G
              Ge +G Gs  ≤[ ≤G-reflexive (+G-comm Ge Gs) ]G
              Gs +G Ge  ≤[ resWasZero s1r +G-mono ≤G-refl Ge ]G
              0G +G Ge  ≤[ ≤G-reflexive (≈G-sym (e0*G Gs) +G-cong ≈G-refl Ge) ]G
        e0 *G Gs +G Ge  ≤G-QED
    ~~>-preservesRes [ the sr ] (upsilon S s) = sr
    ~~>-preservesRes (lam s0r) (lam-cong s0 s1 red) = lam (~~>-preservesRes s0r red)
    ~~>-preservesRes (app split e0r sr) (app1-cong e0 e1 s red) = app split (~~>-preservesRes e0r red) sr
    ~~>-preservesRes (app split er s0r) (app2-cong e s0 s1 red) = app split er (~~>-preservesRes s0r red)
