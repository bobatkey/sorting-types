module LinLambda where

open import Common hiding (Ctx) renaming (_*_ to _×_)

open import Setoid as Setoid'
open import Structure
open import ZeroOneMany using (01ω; 0#; 1#; ω#; 01ωMeetSemilatticeSemiring; _≤01ω_; ≤01ω-refl; ω-bot; _+01ω_; _*01ω_)
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

open import Bidirectional _ 01ωMeetSemilatticeSemiring
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
  app-l : forall {e s} -> x ∈ e -> x ∈ app e s
  app-r : forall {e s} -> x ∈ s -> x ∈ app e s
  lam : forall {s} -> o' x ∈ s -> x ∈ lam s

-- BCI semantics

open import BCI

module WithBCI! {a l} (S : Setoid a l) (Alg : BCI! S) where
  open Setoid S renaming (C to A)
  open BCI! Alg

  toBCI! : forall {n d G} (t : Term n d) -> G |-[ tt ] t -> (1 ≤th n -> A) -> A
  toBCI! (var th) _ f = f th
  toBCI! (app e s) (app split er sr) f = toBCI! e er f · toBCI! s sr f
  toBCI! (pm U e s) r f = {!!}
  toBCI! (proj lr e) r f = {!!}
  toBCI! (case U e s0 s1) r f = {!!}
  toBCI! (bm T e s) r f = {!!}
  toBCI! (the S s) r f = {!!}
  toBCI! (lam s) (lam sr) f = {!!}
  toBCI! (ten s0 s1) r f = {!!}
  toBCI! (wth s0 s1) r f = {!!}
  toBCI! (inj lr s) r f = {!!}
  toBCI! (bang rho s) r f = {!!}
  toBCI! [ e ] r f = {!!}
