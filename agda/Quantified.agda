open import Setoid as Setoid'
open import Structure

module Quantified {c l l'} (S : Setoid c l) (MSS : MeetSemilatticeSemiring S l') where

open Setoid S
open MeetSemilatticeSemiring MSS

open import Common
  hiding (refl; sym; trans; LTy; KEY; LIST; _<**>_; _&_; _-o_)
  renaming (_*_ to _×_)
open import FunctionProperties
open Structure S

--------------------------------------------------------------------------------
-- terms are written without explicit context splitting,
-- and then have resources checked

infixr 30 _-o_ _-[_]o_ _<**>_ _&_
data QTy : Set c where
  KEY         : QTy
  LIST        : QTy -> QTy
  _<**>_ _&_  : QTy -> QTy -> QTy
  _-[_]o_     : QTy -> C -> QTy -> QTy
  BANG        : C -> QTy -> QTy

_-o_ : QTy -> QTy -> QTy
_-o_ = _-[ e1 ]o_

data _|-_ (D : List QTy) : QTy -> Set c where
  var     : forall {T}   -> T elem D -> D |- T
  lam     : forall {S T rho} -> (S :: D) |- T -> D |- (S -[ rho ]o T)
  app     : forall {S T rho} -> D |- (S -[ rho ]o T) -> D |- S -> D |- T

  nil     : forall {T}   -> D |- LIST T
  cons    : forall {T}   -> D |- (T -o LIST T -o LIST T)
  foldr   : forall {S T} -> D |- T
                         -> D |- (S -o (LIST S & T) -o T)
                         -> D |- (LIST S -o T)

  cmp     : forall {T}   -> D |- (KEY -o KEY -o ((KEY -o KEY -o T) & (KEY -o KEY -o T)) -o T)

  tensor  : forall {S T} -> D |- S -> D |- T -> D |- (S <**> T)
  pm      : forall {S T U} -> D |- (S <**> T) -> (S :: T :: D) |- U -> D |- U

  _&_     : forall {S T} -> D |- S -> D |- T -> D |- (S & T)
  proj1   : forall {S T} -> D |- (S & T) -> D |- S
  proj2   : forall {S T} -> D |- (S & T) -> D |- T

  bang    : forall {T} rho -> D |- T -> D |- BANG rho T

QCtx : forall {x X} -> List {x} X -> Set _
QCtx = All (\ _ -> C)

emptyQCtx : forall {x X} D -> QCtx {x} {X} D
emptyQCtx nil = nil
emptyQCtx (x :: D) = e0 :: emptyQCtx D

varQCtx : forall {x X D T} -> C -> T elem D -> QCtx {x} {X} D
varQCtx sigma here = sigma :: emptyQCtx _
varQCtx sigma (there e) = e0 :: varQCtx sigma e

linearQCtx : forall {x X} D -> QCtx {x} {X} D
linearQCtx = mapAll (\ _ -> e1) o emptyQCtx

_≈G_ : forall {x X D} -> QCtx {x} {X} D -> QCtx D -> Set _
G ≈G G' = Zip _≈_ (allTags G) (allTags G')

≈G-refl : forall {x X D} (G : QCtx {x} {X} D) -> G ≈G G
≈G-refl nil = nil
≈G-refl (c :: G) = refl :: ≈G-refl G

≈G-sym : forall {x X D} {G G' : QCtx {x} {X} D} -> G ≈G G' -> G' ≈G G
≈G-sym {G = nil} {nil} nil = nil
≈G-sym {G = p :: G} {p' :: G'} (eq :: eqs) = sym eq :: ≈G-sym eqs

≈G-trans : forall {x X D} {G G' G'' : QCtx {x} {X} D} -> G ≈G G' -> G' ≈G G'' -> G ≈G G''
≈G-trans {G = nil} {nil} {nil} nil nil = nil
≈G-trans {G = p :: G} {p' :: G'} {p'' :: G''} (eq :: eqs) (eq' :: eqs') =
  trans eq eq' :: ≈G-trans eqs eqs'

G-setoid : forall {x X} -> List {x} X -> Setoid (c ⊔ x) (c ⊔ l)
G-setoid D = record
  { C = QCtx D
  ; setoidOver = record
    { _≈_ = _≈G_
    ; isSetoid = record
      { refl = \ {x} -> ≈G-refl x
      ; sym = ≈G-sym
      ; trans = ≈G-trans
      }
    }
  }

_≤G_ : forall {x X D} -> QCtx {x} {X} D -> QCtx D -> Set _
G ≤G G' = Zip _≤_ (allTags G) (allTags G')

≤G-refl : forall {x X D} (G : QCtx {x} {X} D) -> G ≤G G
≤G-refl nil = nil
≤G-refl (p :: G) = ≤-refl :: ≤G-refl G

≤G-reflexive : forall {x X D} {G G' : QCtx {x} {X} D} -> G ≈G G' -> G ≤G G'
≤G-reflexive {G = nil} {nil} nil = nil
≤G-reflexive {G = p :: G} {p' :: G'} (eq :: eqs) = ≤-reflexive eq :: ≤G-reflexive eqs

≤G-trans : forall {x X D} {G0 G1 G2 : QCtx {x} {X} D} ->
           G0 ≤G G1 -> G1 ≤G G2 -> G0 ≤G G2
≤G-trans {G0 = nil} {nil} {nil} nil nil = nil
≤G-trans {G0 = p0 :: G0} {p1 :: G1} {p2 :: G2} (le01 :: le01s) (le12 :: le12s) =
  ≤-trans le01 le12 :: ≤G-trans le01s le12s

_+G_ : forall {x X D} -> QCtx {x} {X} D -> QCtx D -> QCtx D
_+G_ = zipAll _+_

+G-identity : forall {x X} (D : List {x} X) -> Identity (G-setoid D) _+G_ (emptyQCtx D)
+G-identity {x} {X} _ = left , right
  where
  left : {D : List X} -> IdentityLeft (G-setoid D) _+G_ (emptyQCtx D)
  left nil = nil
  left (p :: G) = fst +-identity p :: left G

  right : {D : List X} -> IdentityRight (G-setoid D) _+G_ (emptyQCtx D)
  right nil = nil
  right (p :: G) = snd +-identity p :: right G

_+G-cong_ : forall {x X D} {G0 G0' G1 G1' : QCtx {x} {X} D} ->
            G0 ≈G G0' -> G1 ≈G G1' -> (G0 +G G1) ≈G (G0' +G G1')
_+G-cong_ {D = nil} {nil} {nil} {nil} {nil} nil nil = nil
_+G-cong_ {D = S :: D} {g0 :: G0} {g0' :: G0'} {g1 :: G1} {g1' :: G1'} (eq0 :: eqs0) (eq1 :: eqs1) =
  eq0 +-cong eq1 :: (eqs0 +G-cong eqs1)

_+G-mono_ : forall {x X D} {G0 G0' G1 G1' : QCtx {x} {X} D} ->
            G0 ≤G G0' -> G1 ≤G G1' -> (G0 +G G1) ≤G (G0' +G G1')
_+G-mono_ {D = nil} {nil} {nil} {nil} {nil} nil nil = nil
_+G-mono_ {D = S :: D} {g0 :: G0} {g0' :: G0'} {g1 :: G1} {g1' :: G1'} (sub0 :: subs0) (sub1 :: subs1) =
  sub0 +-mono sub1 :: (subs0 +G-mono subs1)

_*G_ : forall {x X D} C -> QCtx {x} {X} D -> QCtx D
rho *G G = mapAll (rho *_) G

_*G-cong_ : forall {x X D rho rho'} {G G' : QCtx {x} {X} D} ->
            rho ≈ rho' -> G ≈G G' -> (rho *G G) ≈G (rho' *G G')
_*G-cong_ {D = nil} {_} {_} {nil} {nil} _ nil = nil
_*G-cong_ {D = S :: D} {_} {_} {g :: G} {g' :: G'} eq0 (eq1 :: eqs1) =
  eq0 *-cong eq1 :: (eq0 *G-cong eqs1)

_*G-mono_ : forall {x X D rho rho'} {G G' : QCtx {x} {X} D} ->
            rho ≤ rho' -> G ≤G G' -> (rho *G G) ≤G (rho' *G G')
_*G-mono_ {D = nil} {_} {_} {nil} {nil} _ nil = nil
_*G-mono_ {D = S :: D} {_} {_} {g :: G} {g' :: G'} le0 (le1 :: sub1) =
  le0 *-mono le1 :: (le0 *G-mono sub1)

e1*G : forall {x X D} (G : QCtx {x} {X} D) -> (e1 *G G) ≈G G
e1*G nil = nil
e1*G (p :: G) = fst *-identity p :: e1*G G

sg->rho : Two -> C
sg->rho tt = e1
sg->rho ff = e0

data _|-[_]_ {D} (G : QCtx D) (sg : Two) : forall {T} -> D |- T -> Set (c ⊔ l ⊔ l') where
  var : forall {T} {e : T elem D} -> G ≤G varQCtx (sg->rho sg) e -> G |-[ sg ] var e
  -- NOTE: check with Bob about sg * rho
  -- just rho didn't seem to work for the identity function
  lam : forall {S T rho} {t : (S :: D) |- T} -> (sg->rho sg * rho :: G) |-[ sg ] t -> G |-[ sg ] lam {rho = rho} t
  app : forall {G0 G1 S T rho} {t0 : D |- (S -[ rho ]o T)} {t1 : D |- S} ->
        G ≈G (G0 +G (rho *G G1)) -> G0 |-[ sg ] t0 -> G1 |-[ sg ] t1 -> G |-[ sg ] app t0 t1

  nil   : forall {T} -> G ≤G emptyQCtx D -> G |-[ sg ] nil {T = T}
  cons  : forall {T} -> G ≤G emptyQCtx D -> G |-[ sg ] cons {T = T}
  foldr : forall {S T} {t0 : D |- T} {t1 : D |- (S -o (LIST S & T) -o T)} ->
          G ≤G emptyQCtx D -> emptyQCtx D |-[ sg ] t0 -> emptyQCtx D |-[ sg ] t1 -> G |-[ sg ] foldr t0 t1

  cmp : forall {T} -> G ≤G emptyQCtx D -> G |-[ sg ] cmp {T = T}

  tensor : forall {G0 G1 S T} {t0 : D |- S} {t1 : D |- T} ->
           G ≈G (G0 +G G1) -> G0 |-[ sg ] t0 -> G1 |-[ sg ] t1 -> G |-[ sg ] tensor t0 t1
  pm     : forall {G0 G1 S T U} {t0 : D |- (S <**> T)} {t1 : (S :: T :: D) |- U} ->
           G ≈G (G0 +G G1) -> G0 |-[ sg ] t0 -> (sg->rho sg :: sg->rho sg :: G1) |-[ sg ] t1 -> G |-[ sg ] pm t0 t1

  _&_   : forall {S T} {t0 : D |- S} {t1 : D |- T} -> G |-[ sg ] t0 -> G |-[ sg ] t1 -> G |-[ sg ] (t0 & t1)
  proj1 : forall {S T} {t : D |- (S & T)} -> G |-[ sg ] t -> G |-[ sg ] proj1 t
  proj2 : forall {S T} {t : D |- (S & T)} -> G |-[ sg ] t -> G |-[ sg ] proj2 t

  bang  : forall {G' T rho} {t : D |- T} ->
          G ≈G (rho *G G') -> G' |-[ sg ] t -> G |-[ sg ] bang rho t

id-t : forall T -> nil |- (T -o T)
id-t T = lam (var here)

id-r : forall sg T -> nil |-[ sg ] id-t T
id-r sg T = lam (var (≤-reflexive (snd *-identity _) :: nil))

-- strictly linear application is a common special case
app1 : forall {D G G0 G1 sg S T} {t0 : D |- (S -[ e1 ]o T)} {t1 : D |- S} ->
       G ≈G (G0 +G G1) -> G0 |-[ sg ] t0 -> G1 |-[ sg ] t1 -> G |-[ sg ] app t0 t1
app1 {G = G} {G0} {G1} eq r0 r1 = app (≈G-trans eq (≈G-refl G0 +G-cong ≈G-sym (e1*G G1))) r0 r1

app1' : forall {D G G0 G1 sg S T} {t0 : D |- (S -[ e1 ]o T)} {t1 : D |- S} ->
        (G0 +G G1) ≈G G -> G0 |-[ sg ] t0 -> G1 |-[ sg ] t1 -> G |-[ sg ] app t0 t1
app1' = app1 o ≈G-sym

-- x : KEY, y : KEY |- [y,x] : LIST KEY
test-list : (KEY :: KEY :: nil) |- LIST KEY
test-list = app (app cons (var (there here))) (app (app cons (var here)) nil)

test-list-r : linearQCtx _ |-[ tt ] test-list
test-list-r = app1' {G0 = e0 :: e1 :: nil} {e1 :: e0 :: nil}
                    (fst +-identity e1 :: snd +-identity e1 :: nil)
                    (app1' {G0 = e0 :: e0 :: nil} {e0 :: e1 :: nil}
                           (fst +G-identity' (e0 :: e1 :: nil))
                           (cons ≤G-refl')
                           (var ≤G-refl'))
                    (app1' {G0 = e1 :: e0 :: nil} {e0 :: e0 :: nil}
                           (snd +G-identity' (e1 :: e0 :: nil))
                           (app1' {G0 = e0 :: e0 :: nil} {e1 :: e0 :: nil}
                                  (fst +G-identity' (e1 :: e0 :: nil))
                                  (cons ≤G-refl')
                                  (var ≤G-refl'))
                           (nil ≤G-refl'))
  where
  ≤G-refl' = \ {G} -> ≤G-refl {X = QTy} {D = KEY :: KEY :: nil} G
  +G-identity' = +G-identity (KEY :: KEY :: nil)

≈G-subst : forall {D T} {G G' : QCtx D} {t : D |- T} {sg} ->
           G' ≈G G -> G |-[ sg ] t -> G' |-[ sg ] t
≈G-subst eq (var sub) = var (≤G-trans (≤G-reflexive eq) sub)
≈G-subst eq (lam r) = lam (≈G-subst (refl :: eq) r)
≈G-subst eq (app split r0 r1) =
  app (≈G-trans eq split) (≈G-subst (≈G-refl _) r0) (≈G-subst (≈G-refl _) r1)
≈G-subst eq (nil sub) = nil (≤G-trans (≤G-reflexive eq) sub)
≈G-subst eq (cons sub) = cons (≤G-trans (≤G-reflexive eq) sub)
≈G-subst eq (foldr sub r0 r1) =
  foldr (≤G-trans (≤G-reflexive eq) sub) r0 r1
≈G-subst eq (cmp sub) = cmp (≤G-trans (≤G-reflexive eq) sub)
≈G-subst eq (tensor split r0 r1) = tensor (≈G-trans eq split) r0 r1
≈G-subst eq (pm split r0 r1) = pm (≈G-trans eq split) r0 r1
≈G-subst eq (r0 & r1) = ≈G-subst eq r0 & ≈G-subst eq r1
≈G-subst eq (proj1 r) = proj1 (≈G-subst eq r)
≈G-subst eq (proj2 r) = proj2 (≈G-subst eq r)
≈G-subst eq (bang split r) = bang (≈G-trans eq split) (≈G-subst (≈G-refl _) r)

e0*G : forall {x X D} (G : QCtx {x} {X} D) -> (e0 *G G) ≈G emptyQCtx D
e0*G nil = nil
e0*G (p :: G) = fst annihil p :: e0*G G

*Gempty : forall {x X} rho D -> (rho *G emptyQCtx {x} {X} D) ≈G emptyQCtx D
*Gempty rho nil = nil
*Gempty rho (T :: D) = snd annihil rho :: *Gempty rho D

*G-assoc : forall {x X D} rho rho' (G : QCtx {x} {X} D) ->
           ((rho * rho') *G G) ≈G (rho *G (rho' *G G))
*G-assoc rho rho' nil = nil
*G-assoc rho rho' (p :: G) = *-assoc rho rho' p :: *G-assoc rho rho' G

varQCtx-e0 : forall {x X D T} (e : T elem D) -> varQCtx e0 e ≈G emptyQCtx {x} {X} D
varQCtx-e0 here = refl :: ≈G-refl _
varQCtx-e0 (there e) = refl :: varQCtx-e0 e

contemplate : forall {D T G} {t : D |- T} -> G |-[ tt ] t -> (e0 *G G) |-[ ff ] t
contemplate (var {e = e} sub) = var (≤G-reflexive (≈G-trans (e0*G _) (≈G-sym (varQCtx-e0 e))))
contemplate (lam r) =
  lam (≈G-subst (refl *-cong sym (fst *-identity _) :: ≈G-refl _) (contemplate r))
contemplate {D} (app {rho = rho} split r0 r1) =
  app (≈G-trans (e0*G _)
                (≈G-trans (≈G-sym (fst (+G-identity D) (emptyQCtx D)))
                          (≈G-sym (e0*G _) +G-cong ≈G-sym (*Gempty rho D))))
      (contemplate r0)
      (≈G-subst (≈G-sym (e0*G _)) (contemplate r1))
contemplate (nil emp) = nil (≤G-reflexive (e0*G _))
contemplate (cons emp) = cons (≤G-reflexive (e0*G _))
contemplate (foldr emp r0 r1) =
  foldr (≤G-reflexive (e0*G _))
        (≈G-subst (≈G-sym (e0*G _)) (contemplate r0))
        (≈G-subst (≈G-sym (e0*G _)) (contemplate r1))
contemplate (cmp emp) = cmp (≤G-reflexive (e0*G _))
contemplate (tensor split r0 r1) =
  tensor (≈G-trans (e0*G _) (≈G-sym (fst (+G-identity _) (emptyQCtx _))))
         (≈G-subst (≈G-sym (e0*G _)) (contemplate r0))
         (≈G-subst (≈G-sym (e0*G _)) (contemplate r1))
contemplate {D} (pm {G0 = G0} {G1} {S} {T} split r0 r1) =
  pm (≈G-trans (≈G-sym (fst (+G-identity D) _))
               (≈G-sym (e0*G _) +G-cong e0*G _))
     (contemplate r0)
     (≈G-subst (≈G-sym {D = S :: T :: D}
                       (e0*G {D = S :: T :: D}
                             (sg->rho tt :: sg->rho tt :: G1)))
               (contemplate r1))
contemplate (r0 & r1) = contemplate r0 & contemplate r1
contemplate (proj1 r) = proj1 (contemplate r)
contemplate (proj2 r) = proj2 (contemplate r)
contemplate (bang {rho = rho} split r) =
  bang (≈G-trans (e0*G _) (≈G-trans (≈G-sym (*Gempty _ _))
                                    (refl *G-cong ≈G-sym (e0*G _))))
       (contemplate r)

GoodSums : Set _
GoodSums =
  forall {a b c'} -> c' ≤ (a + b) ->
  Sg _ \ a' -> Sg _ \ b' -> (a' ≤ a) × (b' ≤ b) × (c' ≈ (a' + b'))

GoodProducts : Set _
GoodProducts =
  forall {a b c'} -> c' ≤ (a * b) ->
  Sg _ \ b' -> (b' ≤ b) × (c' ≈ (a * b'))

splitSumQCtx : forall {x X D} {G0 G1 G' : QCtx {x} {X} D} ->
            GoodSums -> G' ≤G (G0 +G G1) ->
            Sg _ \ G0' -> Sg _ \ G1' -> (G0' ≤G G0) × (G1' ≤G G1) × (G' ≈G (G0' +G G1'))
splitSumQCtx {G0 = nil} {nil} {nil} gs nil = nil , nil , nil , nil , nil
splitSumQCtx {G0 = p0 :: G0} {p1 :: G1} {p' :: G'} gs (le :: sub) with gs le | splitSumQCtx gs sub
... | p0' , p1' , le0 , le1 , eq | G0' , G1' , sub0 , sub1 , eqs =
  p0' :: G0' , p1' :: G1' , le0 :: sub0 , le1 :: sub1 , eq :: eqs

splitProductQCtx : forall {x X D rho} {G0 G' : QCtx {x} {X} D} ->
                   GoodProducts -> G' ≤G (rho *G G0) ->
                   Sg _ \ G0' -> (G0' ≤G G0) × (G' ≈G (rho *G G0'))
splitProductQCtx {G0 = nil} {nil} gp nil = nil , nil , nil
splitProductQCtx {G0 = p0 :: G0} {p' :: G'} gp (le :: sub) with gp le | splitProductQCtx gp sub
... | p0' , le0 , eq | G0' , sub0 , eqs = p0' :: G0' , le0 :: sub0 , eq :: eqs

meetG : forall {x X D} (G G' : QCtx {x} {X} D) -> QCtx D
meetG = zipAll meet

lowerBoundG : forall {x X D} -> ((G0 G1 : QCtx {x} {X} D) -> meetG G0 G1 ≤G G0)
                              × ((G0 G1 : QCtx {x} {X} D) -> meetG G0 G1 ≤G G1)
lowerBoundG = f , s
  where
  f : forall {x X D} (G0 G1 : QCtx {x} {X} D) -> meetG G0 G1 ≤G G0
  f nil nil = nil
  f (p0 :: G0) (p1 :: G1) = fst lowerBound p0 p1 :: f G0 G1

  s : forall {x X D} (G0 G1 : QCtx {x} {X} D) -> meetG G0 G1 ≤G G1
  s nil nil = nil
  s (p0 :: G0) (p1 :: G1) = snd lowerBound p0 p1 :: s G0 G1

greatestG : forall {x X D} {G0 G1 G : QCtx {x} {X} D} ->
            G ≤G G0 -> G ≤G G1 -> G ≤G meetG G0 G1
greatestG {G0 = nil} {nil} {nil} nil nil = nil
greatestG {G0 = _ :: _} {_ :: _} {_ :: _} (le0 :: sub0) (le1 :: sub1) =
  greatest le0 le1 :: greatestG sub0 sub1

module Good (gs : GoodSums) (gp : GoodProducts) where

  weaken : forall {D T G G' sg} {t : D |- T} ->
           G' ≤G G -> G |-[ sg ] t -> G' |-[ sg ] t
  weaken sub (var sub') = var (≤G-trans sub sub')
  weaken sub (lam r) = lam (weaken (≤-refl :: sub) r)
  weaken sub (app split r0 r1)
    with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
  ... | G0' , rho*G1' , sub0 , rho*sub1 , eqs with splitProductQCtx gp rho*sub1
  ... | G1' , sub1 , eqs1 =
    app {G0 = G0'} {G1'} (≈G-trans eqs (≈G-refl _ +G-cong eqs1))
                         (weaken sub0 r0)
                         (weaken sub1 r1)
  weaken sub (nil emp) = nil (≤G-trans sub emp)
  weaken sub (cons emp) = cons (≤G-trans sub emp)
  weaken sub (foldr emp r0 r1) = foldr (≤G-trans sub emp) r0 r1
  weaken sub (cmp emp) = cmp (≤G-trans sub emp)
  weaken sub (tensor split r0 r1)
    with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
  ... | G0' , G1' , sub0 , sub1 , eqs =
    tensor eqs (weaken sub0 r0) (weaken sub1 r1)
  weaken sub (pm split r0 r1)
    with splitSumQCtx gs (≤G-trans sub (≤G-reflexive split))
  ... | G0' , G1' , sub0 , sub1 , eqs =
    pm eqs (weaken sub0 r0) (weaken (≤-refl :: ≤-refl :: sub1) r1)
  weaken sub (r0 & r1) = weaken sub r0 & weaken sub r1
  weaken sub (proj1 r) = proj1 (weaken sub r)
  weaken sub (proj2 r) = proj2 (weaken sub r)
  weaken sub (bang split r)
    with splitProductQCtx gp (≤G-trans sub (≤G-reflexive split))
  ... | G'' , sub' , split' = bang split' (weaken sub' r)

  resourcesPrincipal : forall {D T G G' sg} {t : D |- T} ->
                       G |-[ sg ] t -> G' |-[ sg ] t ->
                       Sg _ \ G'' -> (G ≤G G'') × (G' ≤G G'') × (G'' |-[ sg ] t)
  resourcesPrincipal {sg = sg} (var {e = e} sub) (var sub') =
    varQCtx (sg->rho sg) e , sub , sub' , var (≤G-refl _)
  resourcesPrincipal (lam r) (lam r') with resourcesPrincipal r r'
  ... | (p'' :: G'') , (le :: sub) , (le' :: sub') , r'' =
    G'' , sub , sub' , lam (weaken (le :: ≤G-refl G'') r'')
  resourcesPrincipal (app {rho = rho} split r0 r1) (app split' r0' r1')
    with resourcesPrincipal r0 r0' | resourcesPrincipal r1 r1'
  ... | G0 , sub0 , sub0' , r0'' | G1 , sub1 , sub1' , r1'' =
    G0 +G (rho *G G1)
    , ≤G-trans (≤G-reflexive split) (sub0 +G-mono (≤-refl *G-mono sub1))
    , ≤G-trans (≤G-reflexive split') (sub0' +G-mono (≤-refl *G-mono sub1'))
    , app (≈G-refl _) r0'' r1''
  resourcesPrincipal (nil emp) (nil emp') = emptyQCtx _ , emp , emp' , nil (≤G-refl _)
  resourcesPrincipal (cons emp) (cons emp') = emptyQCtx _ , emp , emp' , cons (≤G-refl _)
  resourcesPrincipal (foldr emp r0 r1) (foldr emp' r0' r1') =
    emptyQCtx _ , emp , emp' , foldr (≤G-refl _) r0 r1
  resourcesPrincipal (cmp emp) (cmp emp') = emptyQCtx _ , emp , emp' , cmp (≤G-refl _)
  resourcesPrincipal (tensor split r0 r1) (tensor split' r0' r1')
    with resourcesPrincipal r0 r0' | resourcesPrincipal r1 r1'
  ... | G0 , sub0 , sub0' , r0'' | G1 , sub1 , sub1' , r1'' =
    G0 +G G1
    , ≤G-trans (≤G-reflexive split) (sub0 +G-mono sub1)
    , ≤G-trans (≤G-reflexive split') (sub0' +G-mono sub1')
    , tensor (≈G-refl _) r0'' r1''
  resourcesPrincipal (pm split r0 r1) (pm split' r0' r1')
    with resourcesPrincipal r0 r0' | resourcesPrincipal r1 r1'
  ... | G0 , sub0 , sub0' , r0''
      | p :: q :: G1 , lep :: leq :: sub1 , lep' :: leq' :: sub1' , r1'' =
    G0 +G G1
    , ≤G-trans (≤G-reflexive split) (sub0 +G-mono sub1)
    , ≤G-trans (≤G-reflexive split') (sub0' +G-mono sub1')
    , pm (≈G-refl _) r0'' (weaken (lep :: leq :: ≤G-refl _) r1'')
  resourcesPrincipal {G = G} {G'} (r0 & r1) (r0' & r1')
    with resourcesPrincipal r0 r0' | resourcesPrincipal r1 r1'
  ... | G0 , sub0 , sub0' , r0'' | G1 , sub1 , sub1' , r1'' =
    meetG G0 G1 , greatestG sub0 sub1 , greatestG sub0' sub1'
    , weaken (fst lowerBoundG G0 G1) r0'' & weaken (snd lowerBoundG G0 G1) r1''
  resourcesPrincipal (proj1 r) (proj1 r') with resourcesPrincipal r r'
  ... | G'' , sub , sub' , r'' = G'' , sub , sub' , proj1 r''
  resourcesPrincipal (proj2 r) (proj2 r') with resourcesPrincipal r r'
  ... | G'' , sub , sub' , r'' = G'' , sub , sub' , proj2 r''
  resourcesPrincipal (bang {rho = rho} split r) (bang split' r') with resourcesPrincipal r r'
  ... | G'' , sub , sub' , r'' =
    rho *G G''
    , ≤G-trans (≤G-reflexive split) (≤-refl *G-mono sub)
    , ≤G-trans (≤G-reflexive split') (≤-refl *G-mono sub')
    , bang (≈G-refl _) r''

{-+}
--------------------------------------------------------------------------------
-- we can decide whether a term is resource-correct
-- inferTensorLike is for situations where the resources are split into two (app, tensor, pm)

inferResources : forall {D T} (t : D |- T) -> Dec (Sg _ \ G -> G |-r t)

inferTensorLike : forall {D S T} D0 (t0 : D |- S) (t1 : (D0 ++ D) |- T) ->
                   Dec (Sg _ \ G -> Sg _ \ G0 -> (G0 G=> G) * (G0 |-r t0) *
                                                 ((fullQCtx {l = D0} ++All (G \\ G0)) |-r t1))
inferTensorLike D0 t0 t1 with inferResources t0 | inferResources t1
inferTensorLike D0 t0 t1 | yes (G0 , r0) | yes (G1 , r1) with takeDropAll D0 G1
                                                             | ++All-takeDropAll D0 G1
...   | G10 , G11 | G1eq with ==All? _==Two?_ G10 fullQCtx
                            | ==All? _==Two?_ (zipAll and G0 G11) emptyQCtx
...     | yes full | yes emp =
  yes (zipAll or G0 G11 , G0 , or-G=> G0 G11 , r0
      , subst (_|-r t1)
              (trans (sym G1eq)
                     (cong2 _++All_ full (sym (other-half emp))))
              r1)
...     | yes full | no nemp = no (nemp o f)
  where
  f : (Sg _ \ G -> Sg _ \ G0' -> (G0' G=> G) * (G0' |-r t0)
                               * ((fullQCtx {l = D0} ++All (G \\ G0')) |-r t1)) ->
      zipAll and G0 G11 == emptyQCtx
  f (G , G0' , subres , r0' , r1') rewrite |-r-partialFunction r0 r0' =
    subst (\ x -> zipAll and G0' x == emptyQCtx)
          (sym (snd (++AllInj G10 fullQCtx (trans G1eq (|-r-partialFunction r1 r1')))))
          (separate-partitions subres)
...     | no nfull | b =
  no (nfull o \ { (G , G0' , subres , r0' , r1') ->
                  fst (++AllInj G10 fullQCtx (trans G1eq (|-r-partialFunction r1 r1'))) })
inferTensorLike D0 t0 t1 | yes p | no np =
  no (np o \ { (G , G0 , subres , r0 , r1) -> fullQCtx {l = D0} ++All (G \\ G0) , r1 })
inferTensorLike D0 t0 t1 | no np | b =
  no (np o \ { (G , G0 , subres , r0 , r1) -> G0 , r0 })

inferResources (var x) = yes (singlQCtx x , var)
inferResources (lam t) with inferResources t
... | yes (g :: G , r) = mapDec (\ { refl -> G , lam r }) f (g ==Two? tt)
  where
  f : (Sg _ \ G' -> G' |-r lam t) -> g == tt
  f (G' , lam r') with |-r-partialFunction r r'
  ... | refl = refl
inferResources (lam t) | no np = no (np o \ { (G , lam r) -> tt :: G , r })
inferResources (app t0 t1) =
  mapDec (\ { (G , G0 , subres , r0 , r1) ->
              G , app {subres = fromWitness subres} r0 r1 })
         (\ { (G , app {G0 = G0} {subres = subres} r0 r1) ->
              G , G0 , toWitness subres , r0 , r1 })
         (inferTensorLike nil t0 t1)
inferResources nil = yes (emptyQCtx , nil)
inferResources cons = yes (emptyQCtx , cons)
inferResources (foldr t0 t1) with inferResources t0 | inferResources t1
... | yes (G0 , r0) | yes (G1 , r1)
  with ==All? _==Two?_ G0 emptyQCtx | ==All? _==Two?_ G1 emptyQCtx
...   | yes refl | yes refl = yes (emptyQCtx , foldr r0 r1)
...   | yes p | no np = no (np o \ { (.emptyQCtx , foldr r0' r1') ->
                                     |-r-partialFunction r1 r1' })
...   | no np | b = no (np o \ { (.emptyQCtx , foldr r0' r1') ->
                                 |-r-partialFunction r0 r0' })
inferResources (foldr t0 t1) | yes p | no np =
  no (np o \ { (.emptyQCtx , foldr r0 r1) -> emptyQCtx , r1 })
inferResources (foldr t0 t1) | no np | b =
  no (np o \ { (.emptyQCtx , foldr r0 r1) -> emptyQCtx , r0 })
inferResources cmp = yes (emptyQCtx , cmp)
inferResources (tensor t0 t1) =
  mapDec (\ { (G , G0 , subres , r0 , r1) ->
              G , tensor {subres = fromWitness subres} r0 r1 })
         (\ { (G , tensor {subres = subres} r0 r1) ->
              G , _ , toWitness subres , r0 , r1  })
         (inferTensorLike nil t0 t1)
inferResources (pm {S} {T} t0 t1) =
  mapDec (\ { (G , G0 , subres , r0 , r1) ->
              G , pm {subres = fromWitness subres} r0 r1 })
         (\ { (G , pm {subres = subres} r0 r1) ->
              G , _ , toWitness subres , r0 , r1  })
         (inferTensorLike (S :: T :: nil) t0 t1)
inferResources (t0 & t1) with inferResources t0 | inferResources t1
... | yes (G , r0) | yes (G' , r1) =
  mapDec (\ { refl -> G , r0 & r1 })
         (\ { (G'' , r0' & r1') ->
              trans (|-r-partialFunction r0 r0') (|-r-partialFunction r1' r1) })
         (==All? _==Two?_ G G')
inferResources (t0 & t1) | yes p | no np = no (np o \ { (G , r0 & r1) -> G , r1 })
inferResources (t0 & t1) | no np | b = no (np o \ { (G , r0 & r1) -> G , r0 })
inferResources (proj1 t) =
  mapDec (mapSg id proj1) (mapSg id \ { (proj1 r) -> r }) (inferResources t)
inferResources (proj2 t) =
  mapDec (mapSg id proj2) (mapSg id \ { (proj2 r) -> r }) (inferResources t)

--------------------------------------------------------------------------------
-- insertion sort, but hopefully nicer

infixl 4 _$$_
_$$_ : forall {D S T} -> D |- (S -o T) -> D |- S -> D |- T
_$$_ = app

var! : forall {D} m {less : Auto (m <? length D)} -> D |- (D !! #_ m {less})
var! m = var (_ !!Elem # m)

insert : forall {D} -> D |- (LIST KEY -o KEY -o LIST KEY)
insert = foldr (lam (cons $$ var here $$ nil))
               ((lam (lam (lam (cmp $$ var! 2
                                    $$ var! 0
                                    $$ (lam (lam (cons $$ var! 1
                                                       $$ (proj2 (var! 3) $$ var! 0)))
                                      & lam (lam (cons $$ var! 0
                                                       $$ (cons $$ var! 1
                                                                $$ proj1 (var! 3))))))))))

insertion-sort : forall {D} -> D |- (LIST KEY -o LIST KEY)
insertion-sort = foldr nil (lam (lam (insert $$ proj2 (var! 0) $$ var! 1)))

insertion-sort-r : nil |-r insertion-sort {nil}
insertion-sort-r with byDec (inferResources (insertion-sort {nil}))
... | nil , b = b

--------------------------------------------------------------------------------
-- semantics

[[_]]G : {D : List QTy} -> QCtx D -> Set
[[ nil ]]G = One
[[_]]G {S :: D} (tt :: G) = [[ S ]]T * [[ G ]]G
[[ ff :: G ]]G = [[ G ]]G

[[emptyQCtx]]G : forall D -> [[ emptyQCtx {l = D} ]]G == One
[[emptyQCtx]]G nil = refl
[[emptyQCtx]]G (S :: D) = [[emptyQCtx]]G D

ctxIndex : forall {D T} -> T elem D -> [[ D ]]C -> [[ T ]]T
ctxIndex here (t , d) = t
ctxIndex (there v) (t , d) = ctxIndex v d

[[_]]t : forall {D T} -> D |- T -> [[ D ]]C -> [[ T ]]T
[[ var x ]]t d = ctxIndex x d
[[ lam t ]]t d = \ v -> [[ t ]]t (v , d)
[[ app tf te ]]t d = ([[ tf ]]t d) ([[ te ]]t d)
[[ nil ]]t d = nil
[[ cons ]]t d = _::_
[[ foldr tn tc ]]t d = foldright ([[ tn ]]t d) ([[ tc ]]t d)
[[ cmp ]]t d = compare
[[ tensor tl tr ]]t d = [[ tl ]]t d , [[ tr ]]t d
[[ pm t0 t1 ]]t d with [[ t0 ]]t d
... | s , t = [[ t1 ]]t (s , t , d)
[[ tl & tr ]]t d = [[ tl ]]t d , [[ tr ]]t d
[[ proj1 t ]]t d = fst ([[ t ]]t d)
[[ proj2 t ]]t d = snd ([[ t ]]t d)

split : forall {D G} (G0 : QCtx D) -> G0 G=> G -> [[ G ]]G -> [[ G0 ]]G * [[ G \\ G0 ]]G
split {G = nil} nil subres g = <> , <>
split {G = tt :: G} (p0 :: G0) (imp , subres) (t , g) with split G0 subres g
split {_} {tt :: G} (tt :: G0) (imp , subres) (t , g) | g0 , g1 = (t , g0) , g1
split {_} {tt :: G} (ff :: G0) (imp , subres) (t , g) | g0 , g1 = g0 , (t , g1)
split {G = ff :: G} (tt :: G0) (imp , subres) g = Zero-elim (imp <>)
split {G = ff :: G} (ff :: G0) (imp , subres) g = split G0 subres g

empty\\empty : (D : List QTy) -> emptyQCtx {l = D} \\ emptyQCtx == emptyQCtx
empty\\empty nil = refl
empty\\empty (S :: D) rewrite empty\\empty D = refl

emptyG=>empty : (D : List QTy) -> emptyQCtx {l = D} G=> emptyQCtx
emptyG=>empty nil = <>
emptyG=>empty (S :: D) = id , emptyG=>empty D

[[_]]r : forall {D G T} {t : D |- T} -> G |-r t -> [[ G ]]G -> [[ T ]]T
[[ var {T} {e} ]]r = go e
  where
  go : forall {D} (e : T elem D) -> [[ singlQCtx e ]]G -> [[ T ]]T
  go here (t , g) = t
  go (there e) g = go e g
[[ lam r ]]r g = λ s → [[ r ]]r (s , g)
[[ app {G0 = G0} {subres = subres} rf re ]]r g with split G0 (toWitness subres) g
... | g0 , g1 = ([[ rf ]]r g0) ([[ re ]]r g1)
[[ nil ]]r g = nil
[[ cons ]]r g = _::_
[[_]]r {D} (foldr rn rc) g = foldright ([[ rn ]]r g) ([[ rc ]]r g)
[[ cmp ]]r g = compare
[[ tensor {G0 = G0} {subres = subres} rl rr ]]r g with split G0 (toWitness subres) g
... | g0 , g1 = [[ rl ]]r g0 , [[ rr ]]r g1
[[ pm {G0 = G0} {subres = subres} r0 r1 ]]r g with split G0 (toWitness subres) g
... | g0 , g1 with [[ r0 ]]r g0
... | rl , rr = [[ r1 ]]r (rl , rr , g1)
[[ rl & rr ]]r g = [[ rl ]]r g , [[ rr ]]r g
[[ proj1 r ]]r g = fst ([[ r ]]r g)
[[ proj2 r ]]r g = snd ([[ r ]]r g)

sorter : List Nat -> List Nat
sorter = [[ insertion-sort ]]t <>

[_|=_*contains_] : KeySet -> {D : List QTy} (G : QCtx D) -> [[ G ]]G -> Set
[ K |= nil *contains <> ] = nil >< K
[_|=_*contains_] K {S :: D} (tt :: G) (t , g) =
  Sg _ \ K1 -> Sg _ \ K2 -> (K1 ++ K2) >< K * [ K1 |= S contains t ] * [ K2 |= G *contains g ]
[ K |= ff :: G *contains g ] = [ K |= G *contains g ]

[_|=emptyQCtx[_]*contains_] :
  forall K D g -> [ K |= emptyQCtx {l = D} *contains g ] == nil >< K
[ K |=emptyQCtx[ nil ]*contains g ] = refl
[ K |=emptyQCtx[ x :: D ]*contains g ] = [ K |=emptyQCtx[ D ]*contains g ]

record Split {D} (G G0 : QCtx D) (subres : G0 G=> G) (K : List Nat)
             (g0 : [[ G0 ]]G) (g1 : [[ G \\ G0 ]]G) : Set where
  constructor splitting
  field
    K0 : List Nat
    K1 : List Nat
    p : (K0 ++ K1) >< K
    phi0 : [ K0 |= G0 *contains g0 ]
    phi1 : [ K1 |= (G \\ G0) *contains g1 ]

makeSplitting : forall {D} (G G0 : QCtx D) (subres : G0 G=> G)
                (K : List Nat)
                (g : [[ G ]]G) ->
                [ K |= G *contains g ] ->
                let g0 , g1 = split G0 subres g in
                Split G G0 subres K g0 g1
makeSplitting nil nil subres K g phi = splitting nil nil phi permNil permNil
makeSplitting (tt :: G) (p0 :: G0) (imp , subres) K (s , g) (K0 , K1 , p , phi0 , phi1)
  with makeSplitting G G0 subres K1 g phi1
makeSplitting (tt :: G) (tt :: G0) (imp , subres) K (s , g) (K0 , K1 , p , phi0 , phi1)
  | splitting K10 K11 p1 phi10 phi11 =
  splitting (K0 ++ K10) K11
            (permTrans (permAssoc K0 K10 K11)
             (permTrans (permAppR K0 p1)
                        p))
            (K0 , K10 , permRefl _ , phi0 , phi10) phi11
makeSplitting (tt :: G) (ff :: G0) (imp , subres) K (s , g) (K0 , K1 , p , phi0 , phi1)
  | splitting K10 K11 p1 phi10 phi11 =
  splitting K10 (K0 ++ K11)
            (permTrans (permSymm (permAssoc K10 K0 K11))
             (permTrans (permAppL (permSwap++ K10 K0))
              (permTrans (permAssoc K0 K10 K11)
               (permTrans (permAppR K0 p1)
                          p))))
            phi10 (K0 , K11 , permRefl _ , phi0 , phi11)
makeSplitting (ff :: G) (tt :: G0) (imp , subres) K g phi = Zero-elim (imp <>)
makeSplitting (ff :: G) (ff :: G0) (imp , subres) K g phi with makeSplitting G G0 subres K g phi
... | splitting K0 K1 p phi0 phi1 = splitting K0 K1 p phi0 phi1

foldright-welltyped : forall {S T} n c ->
                      [ nil |= T contains n ] ->
                      [ nil |= (S -o (LIST S & T) -o T) contains c ] ->
                      [ nil |= (LIST S -o T) contains foldright n c ]
foldright-welltyped n c phin phic K nil phiss rewrite nilPerm phiss = phin
foldright-welltyped {S} {T} n c phin phic K (s :: ss) (Ks , Kss , p , phis , phiss) =
  preservePerm T _ p
               (phic Ks s phis Kss _
                     (phiss , foldright-welltyped {S} {T} n c phin phic Kss ss phiss))

fundamental : forall {D G T} ->
              {t : D |- T} (r : G |-r t) ->
              forall K g -> [ K |= G *contains g ] -> [ K |= T contains ([[ r ]]r g) ]
fundamental {D} {G} {T} {var e} var = go e
  where
  go : forall {D} (e : T elem D) K g ->
       [ K |= singlQCtx e *contains g ] -> [ K |= T contains [[ var {e = e} ]]r g ]
  go {S :: D} here K (s , g) (K0 , K1 , perm , psi0 , psi1)
    rewrite [ K1 |=emptyQCtx[ D ]*contains g ] | nilPerm psi1 | ++nil K0 =
    preservePerm S s perm psi0
  go (there e) K g phi = go e K g phi
fundamental (lam r) K g phi =
  \ K' s psi -> fundamental r (K ++ K') (s , g) (K' , K , permSwap++ K' K , psi , phi)
fundamental (app {G} {G0} {S = S} {T} {subres = subres} rf re) K g phi
  with makeSplitting G G0 (toWitness subres) K g phi
... | splitting K0 K1 p phi0 phi1 =
  preservePerm T _ p ((fundamental rf K0 _ phi0) _ _ (fundamental re K1 _ phi1))
fundamental {D} nil K g phi rewrite [ K |=emptyQCtx[ D ]*contains g ] = phi
fundamental {D} cons K g phi rewrite [ K |=emptyQCtx[ D ]*contains g ] | nilPerm phi =
  \ K0 s0 phi0 K1 s1 phi1 -> K0 , K1 , permRefl _ , phi0 , phi1
fundamental {D} (foldr {S} {T} rn rc) K g phi
  rewrite [ K |=emptyQCtx[ D ]*contains g ] | nilPerm phi =
  foldright-welltyped {S} {T} _ _
                      (fundamental rn nil _ (subst id
                                                   (sym ([ nil |=emptyQCtx[ D ]*contains _ ]))
                                                   permNil))
                      (fundamental rc nil _ (subst id
                                                   (sym ([ nil |=emptyQCtx[ D ]*contains _ ]))
                                                   permNil))
fundamental {D} {G} {T} (cmp {S}) K g phi K0 s0 phi0 K1 s1 phi1 K2 s2 phi2
  rewrite [ K |=emptyQCtx[ D ]*contains g ] | nilPerm phi with compareNat s0 s1
... | lt .s0 k = preservePerm S _ (lem-2 K0 K1 K2) (snd phi2 K1 s1 phi1 K0 s0 phi0)
... | gte k .s1 = preservePerm S _ (lem-1 K0 K1 K2) (fst phi2 K0 s0 phi0 K1 s1 phi1)
fundamental (tensor {G} {G0} {subres = subres} rl rr) K g phi
  with makeSplitting G G0 (toWitness subres) K g phi
... | splitting K0 K1 p phi0 phi1 =
  K0 , K1 , p , fundamental rl K0 _ phi0 , fundamental rr K1 _ phi1
fundamental (pm {G} {G0} {S} {T} {U} {subres = subres} r0 r1) K g phi
  with makeSplitting G G0 (toWitness subres) K g phi
... | splitting K0 K1 p phi0 phi1
  with fundamental r0 K0 _ phi0
... | K00 , K01 , p0 , phi00 , phi01 =
  preservePerm U _
               (subst (_>< K) (++Assoc K00 K01 K1) (permTrans (permAppL p0) p))
               (fundamental r1 (K00 ++ (K01 ++ K1)) _
                            (K00 , K01 ++ K1 , permRefl _ , phi00
                            , K01 , K1 , permRefl _ , phi01
                            , phi1))
fundamental (rl & rr) K g phi = fundamental rl K g phi , fundamental rr K g phi
fundamental (proj1 r) K g phi = fst (fundamental r K g phi)
fundamental (proj2 r) K g phi = snd (fundamental r K g phi)

isPermutation : forall {t : nil |- (LIST KEY -o LIST KEY)} (r : nil |-r t) l ->
                ([[ r ]]r <> l) >< l
isPermutation r l = repList l ([[ r ]]r <> l) (fundamental r nil <> permNil l l (listRep l))
--  where
--  dummy : Nat
--  dummy = {!fundamental {nil} {nil} {LIST KEY -o LIST KEY} r nil <> permNil!}
{+-}
