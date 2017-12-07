module LinLambdaSmall where

open import Common hiding (Ctx) renaming (_*_ to _×_)

open import Setoid as Setoid'
open import Structure
open import ZeroOneMany --using (01ω; 0#; 1#; ω#; 01ωMeetSemilatticeSemiring; _≤01ω_; ≤01ω-refl; ω-bot; _+01ω_; _*01ω_)
open MeetSemilatticeSemiring 01ωMeetSemilatticeSemiring

_==?_ : (x y : 01ω) -> Dec (x == y)
0# ==? 0# = yes refl
0# ==? 1# = no (λ ())
0# ==? ω# = no (λ ())
1# ==? 0# = no (λ ())
1# ==? 1# = yes refl
1# ==? ω# = no (λ ())
ω# ==? 0# = no (λ ())
ω# ==? 1# = no (λ ())
ω# ==? ω# = yes refl

_≤?_ : (x y : 01ω) -> Dec (x ≤ y)
0# ≤? 0# = yes ≤01ω-refl
0# ≤? 1# = no (λ ())
0# ≤? ω# = no (λ ())
1# ≤? 0# = no (λ ())
1# ≤? 1# = yes ≤01ω-refl
1# ≤? ω# = no (λ ())
ω# ≤? y = yes ω-bot

open import BidirectionalSmall _ 01ωMeetSemilatticeSemiring
open DecEq _==?_
open DecLE _≤?_

id-s : forall {n} -> Term n chk
id-s = lam [ var (os (z≤th _)) ]

id-t : forall {n} (D : Ctx n) S -> D |- S ~> S ∋ id-s
id-t D S with S ==QTy? S | inspect (checkType D (S ~> S)) id-s
id-t D S | yes p | ingraph req = toWitness (subst (T o floor) (sym req) <>)
id-t D S | no np | ingraph req = Zero-elim (np refl)

id-r : forall {n sg} -> Sg _ \ G -> G |-[ sg ] id-s {n}
id-r {n} {tt} = mapSg id fst (byDec (bestRes? {n} tt id-s))
id-r {n} {ff} = mapSg id fst (byDec (bestRes? {n} ff id-s))
--id-r {n} {sg} with sg->rho sg ≤? sg->rho sg | inspect (bestRes? {n} sg) id-s
--... | yes p | ingraph req = {!req!}
--... | no np | b = {!np!}

test : QTy -> Set
test S = {!checkType nil (BANG ω# BASE ~> BASE) (lam [ bm S (var (os (z≤th _))) [ var (os (z≤th _)) ] ])!}

id!-s : forall {n} -> QTy -> Term n chk
id!-s S = lam [ bm S (var (os (z≤th _))) [ var (os (z≤th _)) ] ]

id!-t : forall {n} (D : Ctx n) S -> D |- BANG ω# S ~> S ∋ id!-s S
--id!-t D S = lam [ bm var [ var ] ]
id!-t D S with S ==QTy? S | inspect (checkType D (BANG ω# S ~> S)) (id!-s S)
id!-t D S | yes _ | ingraph req with S ==QTy? S
id!-t D S | yes _ | ingraph req | yes _ = toWitness (subst (T o floor) (sym req) <>)
id!-t D S | yes _ | ingraph req | no np = Zero-elim (np refl)
id!-t D S | no np | ingraph req = Zero-elim (np refl)

data _∈_ {n} (x : 1 ≤th n) : forall {d} -> Term n d -> Set where
  var : x ∈ var x
  app-e : forall {e s} -> x ∈ e -> x ∈ app e s
  app-s : forall {e s} -> x ∈ s -> x ∈ app e s
  bm-e : forall {T e s} -> x ∈ e -> x ∈ bm T e s
  bm-s : forall {T e s} -> o' x ∈ s -> x ∈ bm T e s
  the : forall {S s} -> x ∈ s -> x ∈ the S s
  lam : forall {s} -> o' x ∈ s -> x ∈ lam s
  -- occurrences inside a bang other than the identity (bang 1#) don't count/matter
  bang : forall {s} -> x ∈ s -> x ∈ bang 1# s
  [_] : forall {e} -> x ∈ e -> x ∈ [ e ]

module Usage where
  0#-split : forall {n G G0 G1} (i : 1 ≤th n) ->
             G ≤G G0 +G G1 -> 1≤th-index i G == 0# ->
             (1≤th-index i G0 == 0#) × (1≤th-index i G1 == 0#)
  0#-split {G0 = G0} {G1} i split un with 1≤th-indexVZip i split
  ... | z rewrite un | 1≤th-index-vzip i _+_ G0 G1 =
    < fst 0#-sum (1≤th-index i G1) , snd 0#-sum (1≤th-index i G0) >
      (sym (0#-top z))
  {-+}
  0#-split {G0 = G0} {G1} i split un =
    let lemma = sym (0#-top (≤-trans (≤-reflexive (sym un)) (≤-trans (1≤th-indexVZip i split) (≤-reflexive (≤1th-index-vzip i _+_ G0 G1))))) in
    fst 0#-sum (1≤th-index i G1) lemma , snd 0#-sum (1≤th-index i G0) lemma
  {+-}

  0#-not-appears : forall {n d G i} {t : Term n d} ->
                   G |-[ tt ] t -> 1≤th-index i G == 0# -> i ∈ t -> Zero
  0#-not-appears {G = G} {i} (var sub) un var
    with 1≤th-index i G
       | (≤-trans (1≤th-indexVZip i sub) (≤-reflexive (1≤th-index-varQCtx i)))
  0#-not-appears {G = G} {i} (var sub) refl var | .0# | ()
  0#-not-appears {i = i} (app split er sr) un (app-e el) =
    0#-not-appears er (fst (0#-split i split un)) el
  0#-not-appears {i = i} (app split er sr) un (app-s el) =
    0#-not-appears sr (snd (0#-split i split un)) el
  0#-not-appears {i = i} (bm split er sr) un (bm-e el) =
    0#-not-appears er (fst (0#-split i split un)) el
  0#-not-appears {i = i} (bm split er sr) un (bm-s el) =
    0#-not-appears sr (snd (0#-split i split un)) el
  0#-not-appears (the sr) un (the el) = 0#-not-appears sr un el
  0#-not-appears (lam sr) un (lam el) = 0#-not-appears sr un el
  0#-not-appears {G = G} {i} (bang {Gs = Gs} split sr) un (bang el) =
    0#-not-appears sr un' el
    where
    un' : 1≤th-index i Gs == 0#
    un' with 1≤th-indexVZip i split
    ... | z rewrite 1≤th-index-vmap i id Gs | un = sym (0#-top z)
  --0#-not-appears {G = G} {i} (bang {Gs = Gs} {rho = rho} split sr) un (bang el) =
  --  0#-not-appears sr un' el
  --  where
  --  un' : 1≤th-index i Gs == 0#
  --  un' with 1≤th-indexVZip i split
  --  ... | z rewrite un | 1≤th-index-vmap i (rho *_) Gs = {!0#-top z!}
  0#-not-appears [ er ] un [ el ] = 0#-not-appears er un el

  1#-appears-once : forall {n d G i} {t : Term n d} ->
                    G |-[ tt ] t -> 1≤th-index i G == 1# ->
                    Sg (i ∈ t) \ el -> (el' : i ∈ t) -> el == el'
  1#-appears-once (var sub) use = {!!}
  1#-appears-once (app split er sr) use = {!!}
  1#-appears-once (bm split er sr) use = {!!}
  1#-appears-once (the sr) use = {!!}
  1#-appears-once (lam sr) use = {!!}
  1#-appears-once (bang {rho = rho} split sr) use with rho ==? 1#
  1#-appears-once {i = i} (bang {Gs = Gs} {rho = .1#} split sr) use | yes refl with 1≤th-indexVZip i split
  ... | z rewrite use | 1≤th-index-vmap i id Gs =
    mapSg bang (\ f -> \ { (bang el) -> cong bang (f el) }) (1#-appears-once sr (sym (1#-top z)))
  1#-appears-once {i = i} (bang {rho = rho} split sr) use | no np = {!!}
  1#-appears-once [ er ] use = {!!}

open Usage using (0#-not-appears)

-- BCI semantics

open import BCI

module WithBCI! {a l} (S : Setoid a l) (Alg : BCI! S) where
  open Setoid S renaming (C to A)
  open BCI! Alg

  toBCI! : forall {n d G} (t : Term n d) -> G |-[ tt ] t -> (1 ≤th n -> A) -> A
  toBCI! (var th) _ f = f th
  toBCI! (app e s) (app split er sr) f = toBCI! e er f · toBCI! s sr f
  toBCI! (bm T e s) r f = {!!}
  toBCI! (the S s) r f = {!!}
  toBCI! (lam s) (lam sr) f = {!!}
  toBCI! (bang rho s) r f = {!!}
  toBCI! [ e ] r f = {!!}
