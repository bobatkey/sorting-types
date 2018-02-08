module LinLambdaTiny where

open import Common hiding (Ctx; [[_]]T) renaming (_*_ to _×_)

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

e0-maximal : forall {x} -> e0 ≤ x -> x == e0
e0-maximal ≤01ω-refl = refl

positive : forall {x y} -> x + y == e0 -> x == e0 × y == e0
positive {0#} {y} eq = refl , eq
positive {1#} {0#} ()
positive {1#} {1#} ()
positive {1#} {ω#} ()
positive {ω#} {y} ()

open import BidirectionalTiny _ 01ωPosemiring
open DecLE _≤?_

id-s : forall {n} -> Term n chk
id-s = lam [ var zeroth ]

id-t : forall {n} (D : Ctx n) S -> D |-t S ~> S ∋ id-s
id-t D S with S ==QTy? S | inspect (checkType D (S ~> S)) id-s
id-t D S | yes p | ingraph req = toWitness (subst (T o floor) (sym req) <>)
id-t D S | no np | ingraph req = Zero-elim (np refl)

id-r : forall {n} -> Sg _ \ G -> G |-r id-s {n}
id-r {n} = mapSg id fst (byDec (bestRes? {n} id-s))

C-s : Term 0 chk
C-s = lam (lam (lam [ app (app (var# 2) [ var# 0 ]) [ var# 1 ] ]))

C-r : nil |-r C-s
C-r = cleanup (fst (snd (byDec (bestRes? C-s))))
  where
  cleanup : forall {d G} {s : Term 0 d} -> G |-r s -> nil |-r s
  cleanup {G = nil} r = r

module Usage where
  data _∈t_ {n} (x : 1 ≤th n) : forall {d} -> Term n d -> Set where
    var : x ∈t var x
    app-e : forall {e s} -> x ∈t e -> x ∈t app e s
    app-s : forall {e s} -> x ∈t s -> x ∈t app e s
    the : forall {S s} -> x ∈t s -> x ∈t the S s
    lam : forall {s} -> o' x ∈t s -> x ∈t lam s
    [_] : forall {e} -> x ∈t e -> x ∈t [ e ]

  0#-split : forall {n G G0 G1} (i : 1 ≤th n) ->
             G ≤G G0 +G G1 -> 1≤th-index i G == 0# ->
             (1≤th-index i G0 == 0#) × (1≤th-index i G1 == 0#)
  0#-split {G0 = G0} {G1} i split un with 1≤th-indexVZip i split
  ... | z rewrite un | 1≤th-index-vzip i _+_ G0 G1 =
    < fst 0#-sum (1≤th-index i G1) , snd 0#-sum (1≤th-index i G0) >
      (sym (0#-top z))

  0#-not-appears : forall {n d G i} {t : Term n d} ->
                   G |-r t -> 1≤th-index i G == 0# -> i ∈t t -> Zero
  0#-not-appears {G = G} {i} (var sub) un var
    with 1≤th-index i G
       | (≤-trans (1≤th-indexVZip i sub) (≤-reflexive (1≤th-index-varQCtx i)))
  0#-not-appears {G = G} {i} (var sub) refl var | .0# | ()
  0#-not-appears {i = i} (app split er sr) un (app-e el) =
    0#-not-appears er (fst (0#-split i split un)) el
  0#-not-appears {i = i} (app split er sr) un (app-s el) =
    0#-not-appears sr (snd (0#-split i split un)) el
  0#-not-appears (the sr) un (the el) = 0#-not-appears sr un el
  0#-not-appears (lam sr) un (lam el) = 0#-not-appears sr un el
  0#-not-appears [ er ] un [ el ] = 0#-not-appears er un el

  1#-appears-once : forall {n d G i} {t : Term n d} ->
                    G |-r t -> 1≤th-index i G == 1# ->
                    Sg (i ∈t t) \ el -> (el' : i ∈t t) -> el == el'
  1#-appears-once {G = G} {i = i} (var {th = th} sub) use with i ==th? th
  1#-appears-once {G = G} {.th} (var {th} sub) use | yes refl =
    var , \ { var -> refl }
  1#-appears-once {G = G} {i} (var {th} sub) use | no np
    with 1≤th-indexVZip i sub
  ... | z rewrite use with trans (1#-top z) (1≤th-index-/=-varQCtx np 1#)
  ... | ()
  1#-appears-once {i = i} (app {Ge = Ge} {Gs} split er sr) use with 1≤th-indexVZip i split
  ... | z rewrite use | 1≤th-index-vzip i _+01ω_ Ge Gs
    with 1#-sum (1≤th-index i Ge) (1≤th-index i Gs) (sym (1#-top z))
  ... | inl (usee , uns) =
    mapSg app-e
          (\ f -> \ { (app-e el) -> cong app-e (f el)
                    ; (app-s el) -> Zero-elim (0#-not-appears sr uns el)
                    })
          (1#-appears-once er usee)
  ... | inr (une , uses) =
    mapSg app-s
          (\ f -> \ { (app-e el) -> Zero-elim (0#-not-appears er une el)
                    ; (app-s el) -> cong app-s (f el)
                    })
          (1#-appears-once sr uses)
  1#-appears-once (the sr) use =
    mapSg the (\ f -> \ { (the el) -> cong the (f el) }) (1#-appears-once sr use)
  1#-appears-once (lam sr) use =
    mapSg lam (\ f -> \ { (lam el) -> cong lam (f el) }) (1#-appears-once sr use)
  1#-appears-once [ er ] use =
    mapSg [_] (\ f -> \ { [ el ] -> cong [_] (f el) }) (1#-appears-once er use)

-- BCI semantics

open import BCI as Dummy

module WithBCI {a l} (S : Setoid a l) (Alg : BCI S) where
  open Setoid S renaming (C to A; refl to refl-≈; sym to sym-≈; trans to trans-≈)
  open BCI Alg

  infixl 8 _·s_ _·s-l_ _·s-r_
  infix 4 _∉s_ _∈!s_

  data BCIs (n : Nat) : Set where
    vars : 1 ≤th n -> BCIs n
    Bs Cs Is : BCIs n
    _·s_ : (M N : BCIs n) -> BCIs n

  ⟦_⟧ : forall {n} -> BCIs n -> (1 ≤th n -> A) -> A
  ⟦ vars x ⟧ f = f x
  ⟦ Bs ⟧ f = B
  ⟦ Cs ⟧ f = C
  ⟦ Is ⟧ f = I
  ⟦ M ·s N ⟧ f = ⟦ M ⟧ f · ⟦ N ⟧ f

  data _∉s_ {n : Nat} (x : 1 ≤th n) : BCIs n -> Set where
    vars : forall {y} -> x /= y -> x ∉s vars y
    Bs : x ∉s Bs
    Cs : x ∉s Cs
    Is : x ∉s Is
    _·s_ : forall {M N} -> x ∉s M -> x ∉s N -> x ∉s M ·s N

  data _∈!s_ {n : Nat} (x : 1 ≤th n) : BCIs n -> Set where
    vars : x ∈!s vars x
    _·s-l_ : forall {M N} -> x ∈!s M -> x ∉s N -> x ∈!s M ·s N
    _·s-r_ : forall {M N} -> x ∉s M -> x ∈!s N -> x ∈!s M ·s N

  punchUp : forall {n} -> A -> (1 ≤th n -> A) -> 1 ≤th succ n -> A
  punchUp a f (os i) = a
  punchUp a f (o' i) = f i

  elimUnused : forall {n} {M : BCIs (succ n)} -> zeroth ∉s M -> BCIs n
  elimUnused {M = vars (os y)} (vars neq) = Zero-elim (neq (cong os (z≤th-unique _ y)))
  elimUnused {M = vars (o' y)} (vars neq) = vars y
  elimUnused Bs = Bs
  elimUnused Cs = Cs
  elimUnused Is = Is
  elimUnused (nonl ·s nonr) = elimUnused nonl ·s elimUnused nonr

  elimUnusedEq : forall {n} {M : BCIs (succ n)} (non : zeroth ∉s M) f a ->
                 ⟦ elimUnused non ⟧ f ≈ ⟦ M ⟧ (punchUp a f)
  elimUnusedEq {M = vars (os y)} (vars neq) f a = aboutZero \ b -> ⟦ Zero-elim b ⟧ f ≈ a
  elimUnusedEq {M = vars (o' y)} (vars neq) f a = refl-≈
  elimUnusedEq Bs f a = refl-≈
  elimUnusedEq Cs f a = refl-≈
  elimUnusedEq Is f a = refl-≈
  elimUnusedEq (nonl ·s nonr) f a = elimUnusedEq nonl f a ·-cong elimUnusedEq nonr f a

  elimUnusedUnused : forall {n} {M : BCIs (succ n)} (non : zeroth ∉s M)
                     {x} -> o' x ∉s M -> x ∉s elimUnused non
  elimUnusedUnused {M = vars (os y)} (vars _) nin = aboutZero \ b -> _ ∉s Zero-elim b
  elimUnusedUnused {n} {vars (o' y)} (vars _) {x} (vars neq) = vars (neq o cong o')
  elimUnusedUnused Bs nin = Bs
  elimUnusedUnused Cs nin = Cs
  elimUnusedUnused Is nin = Is
  elimUnusedUnused (nonl ·s nonr) (ninl ·s ninr) =
    elimUnusedUnused nonl ninl ·s elimUnusedUnused nonr ninr

  elimUnusedUsed : forall {n} {M : BCIs (succ n)} (non : zeroth ∉s M)
                   {x} -> o' x ∈!s M -> x ∈!s elimUnused non
  elimUnusedUsed (vars neq) vars = vars
  elimUnusedUsed Bs ()
  elimUnusedUsed Cs ()
  elimUnusedUsed Is ()
  elimUnusedUsed (nonl ·s nonr) (one ·s-l nin) =
    elimUnusedUsed nonl one ·s-l elimUnusedUnused nonr nin
  elimUnusedUsed (nonl ·s nonr) (nin ·s-r one) =
    elimUnusedUnused nonl nin ·s-r elimUnusedUsed nonr one

  elimUsed : forall {n} {M : BCIs (succ n)} -> zeroth ∈!s M -> BCIs n
  elimUsed vars = Is
  elimUsed (uni ·s-l non) = Cs ·s elimUsed uni ·s elimUnused non
  elimUsed (non ·s-r uni) = Bs ·s elimUnused non ·s elimUsed uni

  elimUsedEq : forall {n} {M : BCIs (succ n)} (uni : zeroth ∈!s M) f a ->
                   ⟦ elimUsed uni ⟧ f · a ≈ ⟦ M ⟧ (punchUp a f)
  elimUsedEq vars f a = Ix a
  elimUsedEq (uni ·s-l non) f a =
    trans-≈ (Cxyz _ _ a) (elimUsedEq uni f a ·-cong elimUnusedEq non f a)
  elimUsedEq (non ·s-r uni) f a =
    trans-≈ (Bxyz _ _ a) (elimUnusedEq non f a ·-cong elimUsedEq uni f a)

  elimUsedUnused : forall {n} {M : BCIs (succ n)} (uni : zeroth ∈!s M)
                       {x} -> o' x ∉s M -> x ∉s elimUsed uni
  elimUsedUnused vars nin = Is
  elimUsedUnused (uni ·s-l non) (ninl ·s ninr) =
    Cs ·s elimUsedUnused uni ninl ·s elimUnusedUnused non ninr
  elimUsedUnused (non ·s-r uni) (ninl ·s ninr) =
    Bs ·s elimUnusedUnused non ninl ·s elimUsedUnused uni ninr

  elimUsedUsed : forall {n} {M : BCIs (succ n)} (uni : zeroth ∈!s M)
                 {x} -> o' x ∈!s M -> x ∈!s elimUsed uni
  elimUsedUsed vars ()
  elimUsedUsed (uni ·s-l non) (one ·s-l nin) =
    Cs ·s-r elimUsedUsed uni one ·s-l elimUnusedUnused non nin
  elimUsedUsed (uni ·s-l non) (nin ·s-r one) =
    Cs ·s elimUsedUnused uni nin ·s-r elimUnusedUsed non one
  elimUsedUsed (non ·s-r uni) (one ·s-l nin) =
    Bs ·s-r elimUnusedUsed non one ·s-l elimUsedUnused uni nin
  elimUsedUsed (non ·s-r uni) (nin ·s-r one) =
    Bs ·s elimUnusedUnused non nin ·s-r elimUsedUsed uni one

  UsageMatch : forall {n} (G : QCtx n) (M : BCIs n) -> Set
  UsageMatch G M = forall x -> case 1≤th-index x G of \ { 0# -> x ∉s M
                                                        ; 1# -> x ∈!s M
                                                        ; ω# -> One
                                                        }

  toBCIs : forall {n d G} {t : Term n d} -> G |-r t -> BCIs n
  toBCIsUsage : forall {n d G} {t : Term n d}
                (tr : G |-r t) -> UsageMatch G (toBCIs tr)

  toBCIs {t = var i} (var sub) = vars i
  toBCIs (app split er sr) = toBCIs er ·s toBCIs sr
  toBCIs (the sr) = toBCIs sr
  toBCIs (lam sr) = elimUsed (toBCIsUsage sr zeroth)
  toBCIs [ er ] = toBCIs er

  toBCIsUsage {G = G} (var {i} sub) j with j ==th? i | 1≤th-indexVZip j sub
  toBCIsUsage {G = G} (var {.j} sub) j | yes refl | le
    rewrite 1≤th-index-varQCtx {rho = 1#} j with 1≤th-index j G
  toBCIsUsage {G = G} (var {.j} sub) j | yes refl | () | 0#
  ... | 1# = vars
  ... | ω# = <>
  toBCIsUsage {G = G} (var {i} sub) j | no neq | le
    rewrite 1≤th-index-/=-varQCtx neq 1# with 1≤th-index j G
  ... | 0# = vars neq
  toBCIsUsage {G = G} (var {i} sub) j | no neq | () | 1#
  ... | ω# = <>
  toBCIsUsage {G = G} (app {Ge = Ge} {Gs} split er sr) i
    with 1≤th-indexVZip i split
  ... | a rewrite 1≤th-index-vzip i _+01ω_ Ge Gs with 1≤th-index i G
  toBCIsUsage {G = G} (app {Ge} {Gs} split er sr) i
      | ≤01ω-refl | .(1≤th-index i Ge +01ω 1≤th-index i Gs)
    with 1≤th-index i Ge | 1≤th-index i Gs | toBCIsUsage er i | toBCIsUsage sr i
  ... | 0# | 0# | eu | su = eu ·s su
  ... | 0# | 1# | eu | su = eu ·s-r su
  ... | 0# | ω# | eu | su = <>
  ... | 1# | 0# | eu | su = eu ·s-l su
  ... | 1# | 1# | eu | su = <>
  ... | 1# | ω# | eu | su = <>
  ... | ω# | _ | eu | su = <>
  toBCIsUsage {G = G} (app {Ge} {Gs} split er sr) i | ω-bot | .ω# = <>
  toBCIsUsage (the sr) = toBCIsUsage sr
  toBCIsUsage {G = G} (lam sr) i
    with 1≤th-index i G | toBCIsUsage sr zeroth | toBCIsUsage sr (o' i)
  ... | 0# | h | t = elimUsedUnused h t
  ... | 1# | h | t = elimUsedUsed h t
  ... | ω# | h | t = <>
  toBCIsUsage [ er ] = toBCIsUsage er

  toBCI : forall {n d G} {t : Term n d} -> G |-r t -> (1 ≤th n -> A) -> A
  toBCI tr f = ⟦ toBCIs tr ⟧ f


  -- Typed BCI

  infix 4 _|-s_::_
  data _|-s_::_ {n} (D : Ctx n) : BCIs n -> QTy -> Set where
    vars : forall i -> D |-s vars i :: 1≤th-index i D
    Bs : forall {S T U} -> D |-s Bs :: (T ~> U) ~> (S ~> T) ~> (S ~> U)
    Cs : forall {S T U} -> D |-s Cs :: (S ~> T ~> U) ~> (T ~> S ~> U)
    Is : forall {S} -> D |-s Is :: S ~> S
    _·s_ : forall {S T a b} ->
           D |-s a :: S ~> T -> D |-s b :: S -> D |-s a ·s b :: T

  elimUnusedTy : forall {n D S T} {M : BCIs (succ n)} (non : zeroth ∉s M) ->
                 S :: D |-s M :: T -> D |-s elimUnused non :: T
  elimUnusedTy (vars neq) (vars (os i)) rewrite z≤th-unique i (z≤th _) =
    Zero-elim (neq refl)
  elimUnusedTy (vars neq) (vars (o' i)) = vars i
  elimUnusedTy Bs Bs = Bs
  elimUnusedTy Cs Cs = Cs
  elimUnusedTy Is Is = Is
  elimUnusedTy (Mnon ·s Nnon) (Mt ·s Nt) =
    elimUnusedTy Mnon Mt ·s elimUnusedTy Nnon Nt

  elimUsedTy : forall {n D S T} {M : BCIs (succ n)} (uni : zeroth ∈!s M) ->
               S :: D |-s M :: T -> D |-s elimUsed uni :: S ~> T
  elimUsedTy vars (vars .zeroth) = Is
  elimUsedTy (uni ·s-l non) (Mt ·s Nt) =
    Cs ·s elimUsedTy uni Mt ·s elimUnusedTy non Nt
  elimUsedTy (non ·s-r uni) (Mt ·s Nt) =
    Bs ·s elimUnusedTy non Mt ·s elimUsedTy uni Nt

  toBCIsTy : forall {n G D d S} {t : Term n d} ->
             (tr : G |-r t) -> D |-t t :-: S -> D |-s toBCIs tr :: S
  toBCIsTy (var sub) (var {i}) = vars i
  toBCIsTy (app split er sr) (app et st) =
    toBCIsTy er et ·s toBCIsTy sr st
  toBCIsTy (the sr) (the st) = toBCIsTy sr st
  toBCIsTy (lam sr) (lam st) =
    elimUsedTy (toBCIsUsage sr zeroth) (toBCIsTy sr st)
  toBCIsTy [ er ] [ et ] = toBCIsTy er et


  -- Semantics

  infix 4 [_]T_≈_ [_]D_≈_

  [[_]]T : QTy -> Set
  [_]T_≈_ : forall A (x y : [[ A ]]T) -> Set

  [[ BASE ]]T = One
  [[ S ~> T ]]T = Sg ([[ S ]]T -> [[ T ]]T) \ f ->
                  forall x y -> [ S ]T x ≈ y -> [ T ]T f x ≈ f y

  [ BASE ]T x ≈ y = One
  [ S ~> T ]T (fx , cx) ≈ (fy , cy) =
    forall x y -> [ S ]T x ≈ y -> [ T ]T fx x ≈ fy y

  infixl 6 _[$]_
  _[$]_ : forall {S T} -> [[ S ~> T ]]T -> [[ S ]]T -> [[ T ]]T
  f [$] x = fst f x

  refl-T≈ : forall {T} x -> [ T ]T x ≈ x
  refl-T≈ {BASE} x = <>
  refl-T≈ {S ~> T} (fx , cx) x y = cx x y

  trans-T≈ : forall {T} x y z -> [ T ]T x ≈ y -> [ T ]T y ≈ z -> [ T ]T x ≈ z
  trans-T≈ {BASE} x y z xy yz = <>
  trans-T≈ {S ~> T} x y z xy yz a b ab =
    trans-T≈ (x [$] a) (y [$] a) (z [$] b) (xy a a (refl-T≈ a)) (yz a b ab)

  [[_]]D : forall {n} -> Ctx n -> Set
  [[ nil ]]D = One
  [[ T :: D ]]D = [[ T ]]T × [[ D ]]D

  [_]D_≈_ : forall {n} (D : Ctx n) (x y : [[ D ]]D) -> Set
  [ nil ]D x ≈ y = One
  [ T :: D ]D (tx , dx) ≈ (ty , dy) = [ T ]T tx ≈ ty × [ D ]D dx ≈ dy

  refl-D≈ : forall {n} {D : Ctx n} x -> [ D ]D x ≈ x
  refl-D≈ {D = nil} <> = <>
  refl-D≈ {D = T :: D} (x , d) = refl-T≈ x , refl-D≈ d

  [[_]]i : forall {n} (i : 1 ≤th n) {D} -> [[ D ]]D -> [[ 1≤th-index i D ]]T
  [[ os i ]]i {T :: D} (t , d) = t
  [[ o' i ]]i {T :: D} (t , d) = [[ i ]]i d

  [[_]]i-D≈ : forall {n} (i : 1 ≤th n) {D} (dx dy : [[ D ]]D) ->
              [ D ]D dx ≈ dy -> [ 1≤th-index i D ]T [[ i ]]i dx ≈ [[ i ]]i dy
  [[ os i ]]i-D≈ {T :: D} _ _ (t , d) = t
  [[ o' i ]]i-D≈ {T :: D} (tx , dx) (ty , dy) (t , d) = [[ i ]]i-D≈ dx dy d

  [[_]]t : forall {n D d S} {t : Term n d} -> D |-t t :-: S -> [[ D ]]D -> [[ S ]]T
  [[_]]t-D≈ : forall {n D d S} {t : Term n d} (tt : D |-t t :-: S)
              dx dy -> [ D ]D dx ≈ dy -> [ S ]T [[ tt ]]t dx ≈ [[ tt ]]t dy

  [[ var {i} ]]t = [[ i ]]i
  [[ app et st ]]t d = [[ et ]]t d [$] [[ st ]]t d
  [[ the st ]]t = [[ st ]]t
  [[ lam st ]]t d = (\ x -> [[ st ]]t (x , d))
                  , \ x y xy -> [[ st ]]t-D≈ (x , d) (y , d) (xy , refl-D≈ d)
  [[ [ et ] ]]t = [[ et ]]t

  [[ var {i} ]]t-D≈ = [[ i ]]i-D≈
  [[ app et st ]]t-D≈ dx dy d =
    ([[ et ]]t-D≈ dx dy d) ([[ st ]]t dx) ([[ st ]]t dy) ([[ st ]]t-D≈ dx dy d)
  [[ the st ]]t-D≈ = [[ st ]]t-D≈
  [[ lam st ]]t-D≈ dx dy d sx sy t = [[ st ]]t-D≈ (sx , dx) (sy , dy) (t , d)
  [[ [ et ] ]]t-D≈ = [[ et ]]t-D≈

  [[_]]c : forall {n D S} {a : BCIs n} -> D |-s a :: S -> [[ D ]]D -> [[ S ]]T
  [[ vars i ]]c = [[ i ]]i
  [[ Bs ]]c d = (\ s -> (\ t -> (\ u -> s [$] (t [$] u))
                               , \ ux uy u -> (refl-T≈ s) (t [$] ux) (t [$] uy)
                                                          ((refl-T≈ t) ux uy u))
                       , \ tx ty t ux uy u -> (refl-T≈ s) (tx [$] ux) (ty [$] uy)
                                                          (t ux uy u))
               , \ sx sy s tx ty t ux uy u -> s (tx [$] ux) (ty [$] uy)
                                                (t ux uy u)
  [[ Cs ]]c d = (\ s -> (\ t -> (\ u -> s [$] u [$] t)
                               , \ ux uy u -> (refl-T≈ s) ux uy u
                                                          t  t  (refl-T≈ t))
                       , \ tx ty t ux uy u -> (refl-T≈ s) ux uy u tx ty t)
               , \ sx sy s tx ty t ux uy u -> s ux uy u tx ty t
  [[ Is ]]c d = (\ s -> s) , \ sx sy s -> s
  [[ at ·s bt ]]c d = [[ at ]]c d [$] [[ bt ]]c d

  elimUnused-T≈ :
    forall {n D S T} {M : BCIs (succ n)} (non : zeroth ∉s M)
    (Mt : S :: D |-s M :: T) (s : [[ S ]]T) (d : [[ D ]]D) ->
    [ T ]T [[ Mt ]]c (s , d) ≈ [[ elimUnusedTy non Mt ]]c d
  elimUnused-T≈ (vars neq) (vars (os i)) s d rewrite z≤th-unique i (z≤th _) =
    Zero-elim (neq refl)
  elimUnused-T≈ (vars neq) (vars (o' i)) s d = refl-T≈ ([[ i ]]i d)
  elimUnused-T≈ Bs Bs z d sx sy s tx ty t ux uy u =
    s (tx [$] ux) (ty [$] uy) (t ux uy u)
  elimUnused-T≈ Cs Cs z d sx sy s tx ty t ux uy u = s ux uy u tx ty t
  elimUnused-T≈ Is Is z d sx sy s = s
  elimUnused-T≈ (Mnon ·s Nnon) (Mt ·s Nt) s d =
    (elimUnused-T≈ Mnon Mt s d) ([[ Nt ]]c (s , d))
                                ([[ elimUnusedTy Nnon Nt ]]c d)
                                (elimUnused-T≈ Nnon Nt s d)

  elimUsed-T≈ :
    forall {n D S T} {M : BCIs (succ n)} (uni : zeroth ∈!s M)
    (Mt : S :: D |-s M :: T) (s : [[ S ]]T) (d : [[ D ]]D) ->
    [ T ]T [[ Mt ]]c (s , d) ≈ [[ elimUsedTy uni Mt ]]c d [$] s
  elimUsed-T≈ vars (vars .zeroth) s d = refl-T≈ s
  elimUsed-T≈ (uni ·s-l non) (Mt ·s Nt) s d =
    (elimUsed-T≈ uni Mt s d) ([[ Nt ]]c (s , d))
                             ([[ elimUnusedTy non Nt ]]c d)
                             (elimUnused-T≈ non Nt s d)
  elimUsed-T≈ (non ·s-r uni) (Mt ·s Nt) s d =
    (elimUnused-T≈ non Mt s d) ([[ Nt ]]c (s , d))
                               ([[ elimUsedTy uni Nt ]]c d [$] s)
                               (elimUsed-T≈ uni Nt s d)

  toBCIs-T≈ :
    forall {n G D d S} {u : Term n d} (ur : G |-r u) (ut : D |-t u :-: S) d ->
    [ S ]T [[ ut ]]t d ≈ [[ toBCIsTy ur ut ]]c d
  toBCIs-T≈ (var sub) (var {i}) d = refl-T≈ ([[ i ]]i d)
  toBCIs-T≈ (app split er sr) (app et st) d =
    (toBCIs-T≈ er et d) ([[ st ]]t d) ([[ toBCIsTy sr st ]]c d)
                        (toBCIs-T≈ sr st d)
  toBCIs-T≈ (the sr) (the st) d = toBCIs-T≈ sr st d
  toBCIs-T≈ (lam sr) (lam st) d sx sy s =
    trans-T≈ ([[ st ]]t (sx , d))
             ([[ toBCIsTy sr st ]]c (sx , d))
             ([[ elimUsedTy (toBCIsUsage sr zeroth)
                            (toBCIsTy sr st) ]]c d [$] sy)
             (toBCIs-T≈ sr st (sx , d))
             (trans-T≈ ([[ toBCIsTy sr st ]]c (sx , d))
                       ([[ elimUsedTy (toBCIsUsage sr zeroth)
                                      (toBCIsTy sr st) ]]c d [$] sx)
                       ([[ elimUsedTy (toBCIsUsage sr zeroth)
                                      (toBCIsTy sr st) ]]c d [$] sy)
                       (elimUsed-T≈ (toBCIsUsage sr zeroth)
                                    (toBCIsTy sr st) sx d)
                       ((refl-T≈ ([[ elimUsedTy (toBCIsUsage sr zeroth)
                                                (toBCIsTy sr st) ]]c d))
                                 sx sy s))
  toBCIs-T≈ [ er ] [ et ] d = toBCIs-T≈ er et d

open import BCI.Indexed
open import BCI.Indexed.Ordered

module WithBCIρ≤ {a l} (S : Setoid a l) (Alg : BCIρ≤ S _ posemiring) where
  open Setoid S renaming (C to A; refl to refl-≈; sym to sym-≈; trans to trans-≈)
  open BCIρ≤ Alg
  open WithBCI S bci
  open BCI-Combinators S bci
  open import Assembly bci
  open import Assembly.Indexed bciρ
  open import Assembly.Indexed.Ordered Alg

  -- realisability

  T-asm : QTy -> Assembly (a ⊔ l) (a ⊔ l) (a ⊔ l)
  T-asm BASE = LiftA {r' = a} oneA
  T-asm (S ~> T) = T-asm S ->A T-asm T

  GD-asm : forall {n} (G : QCtx n) (D : Ctx n) -> Assembly _ _ _
  GD-asm nil nil = LiftA {r' = a} oneA
  GD-asm (ρ :: G) (T :: D) = pairA (bangA ρ (T-asm T)) (GD-asm G D)

  sA : forall {n} {G Ge Gs : QCtx n} {D : Ctx n} {S T} -> G ≤G Ge +G Gs ->
       GD-asm Ge D =A> (T-asm S ->A T-asm T) -> GD-asm Gs D =A> T-asm S ->
       GD-asm G D =A> T-asm T
  sA sub F G = record
    { f = record { _$E_ = \ gd -> {!!} ; _$E=_ = {!!} }
    ; af = {!!}
    ; realises = {!!}
    }
    where
    module F = _=A>_ F

  interpret : forall {n G D d T} {t : Term n d} -> G |-r t -> D |-t t :-: T ->
              GD-asm G D =A> T-asm T
  interpret (var sub) (var {th = th}) = record
    { f = f th sub
    ; af = af th
    ; realises = {!!}
    }
    where
    f : forall {n G D} (th : 1 ≤th n) -> G ≤G varQCtx th e1 ->
         Assembly.U (GD-asm G D) ->E Assembly.U (T-asm (1≤th-index th D))
    f {succ n} {rho :: G} {T :: D} (os th) (le :: sub) = fstE
    f {succ n} {rho :: G} {T :: D} (o' th) (le :: sub) = f th sub oE sndE

    af : forall {n} (th : 1 ≤th n) -> A
    af (os th) = {!!}
    af (o' th) = B · af th · appC

    realises : forall {n G D} (th : 1 ≤th n) (sub : G ≤G varQCtx th e1) ->
               let module GD = Assembly (GD-asm G D) in
               let module T = Assembly (T-asm (1≤th-index th D)) in
               forall {u au} -> au GD.|= u -> af th · au T.|= f th sub $E u
    realises {succ n} {rho :: G} {T :: D} (os th) (le :: sub) {uv , uw} {au} (av , aw , auq , rv , rw) =
      {!bangA-≤ le!}
    realises {succ n} {rho :: G} {T :: D} (o' th) (le :: sub) {uv , uw} {au} (av , aw , auq , rv , rw) =
      |=-resp (sym-≈ eq) (Setoid.refl U) (realises th sub rw)
      where
      open Assembly (T-asm (1≤th-index th D)) using (|=-resp; U)
      open SetoidReasoning S

      av≈I : av ≈ I
      av≈I = {!(ρ≤0.realises rv)!}
        where
        module !0 = _=A>_ (bangA-0 (T-asm T))
        module ρ≤0 = _=A>_ (bangA-≤ le (T-asm T))

      eq : B · af th · appC · au ≈ af th · aw
      eq =
        B · af th · appC · au        ≈[ Bxyz (af th) appC au ]≈
        af th · (appC · au)          ≈[ refl-≈ ·-cong
          (appC · au          ≈[ refl-≈ ·-cong auq ]≈
           appC · (av ,C aw)  ≈[ appC-comp av aw ]≈
           av · aw            ≈[ av≈I ·-cong refl-≈ ]≈
           I · aw             ≈[ Ix aw ]≈
           aw                 QED)   ]≈
        af th · aw                   QED
  interpret (app split er sr) (app et st) = {!interpret er et , interpret sr st!}  -- S combinator
  interpret (the sr) (the st) = interpret sr st
  interpret (lam sr) (lam st) = {!interpret sr st!}  -- curry
  interpret [ er ] [ et ] = interpret er et
