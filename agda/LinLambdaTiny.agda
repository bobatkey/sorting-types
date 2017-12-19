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
open ZeroMaximal e0-maximal positive

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

C-s : Term 0 chk
C-s = lam (lam (lam [ app (app (var# 2) [ var# 0 ]) [ var# 1 ] ]))

C-r : nil |-[ tt ] C-s
C-r = cleanup (fst (snd (byDec (bestRes? tt C-s))))
  where
  cleanup : forall {d G} {s : Term 0 d} -> G |-[ tt ] s -> nil |-[ tt ] s
  cleanup {G = nil} r = r

data _∈_ {n} (x : 1 ≤th n) : forall {d} -> Term n d -> Set where
  var : x ∈ var x
  app-e : forall {e s} -> x ∈ e -> x ∈ app e s
  app-s : forall {e s} -> x ∈ s -> x ∈ app e s
  the : forall {S s} -> x ∈ s -> x ∈ the S s
  lam : forall {s} -> o' x ∈ s -> x ∈ lam s
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
  0#-not-appears (the sr) un (the el) = 0#-not-appears sr un el
  0#-not-appears (lam sr) un (lam el) = 0#-not-appears sr un el
  0#-not-appears [ er ] un [ el ] = 0#-not-appears er un el

  1#-appears-once : forall {n d G i} {t : Term n d} ->
                    G |-[ tt ] t -> 1≤th-index i G == 1# ->
                    Sg (i ∈ t) \ el -> (el' : i ∈ t) -> el == el'
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

open Usage using (0#-not-appears)

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

  elimUnused : forall {n} {M : BCIs (succ n)} -> os (z≤th n) ∉s M -> BCIs n
  elimUnused {M = vars (os y)} (vars neq) = Zero-elim (neq (cong os (z≤th-unique _ y)))
  elimUnused {M = vars (o' y)} (vars neq) = vars y
  elimUnused Bs = Bs
  elimUnused Cs = Cs
  elimUnused Is = Is
  elimUnused (nonl ·s nonr) = elimUnused nonl ·s elimUnused nonr

  elimUnusedEq : forall {n} {M : BCIs (succ n)} (non : os (z≤th n) ∉s M) f a ->
                 ⟦ elimUnused non ⟧ f ≈ ⟦ M ⟧ (punchUp a f)
  elimUnusedEq {M = vars (os y)} (vars neq) f a = aboutZero \ b -> ⟦ Zero-elim b ⟧ f ≈ a
  elimUnusedEq {M = vars (o' y)} (vars neq) f a = refl-≈
  elimUnusedEq Bs f a = refl-≈
  elimUnusedEq Cs f a = refl-≈
  elimUnusedEq Is f a = refl-≈
  elimUnusedEq (nonl ·s nonr) f a = elimUnusedEq nonl f a ·-cong elimUnusedEq nonr f a

  elimUnusedUnused : forall {n} {M : BCIs (succ n)} (non : os (z≤th n) ∉s M)
                     {x} -> o' x ∉s M -> x ∉s elimUnused non
  elimUnusedUnused {M = vars (os y)} (vars _) nin = aboutZero \ b -> _ ∉s Zero-elim b
  elimUnusedUnused {n} {vars (o' y)} (vars _) {x} (vars neq) = vars (neq o cong o')
  elimUnusedUnused Bs nin = Bs
  elimUnusedUnused Cs nin = Cs
  elimUnusedUnused Is nin = Is
  elimUnusedUnused (nonl ·s nonr) (ninl ·s ninr) =
    elimUnusedUnused nonl ninl ·s elimUnusedUnused nonr ninr

  elimUnusedUsed : forall {n} {M : BCIs (succ n)} (non : os (z≤th n) ∉s M)
                   {x} -> o' x ∈!s M -> x ∈!s elimUnused non
  elimUnusedUsed (vars neq) vars = vars
  elimUnusedUsed Bs ()
  elimUnusedUsed Cs ()
  elimUnusedUsed Is ()
  elimUnusedUsed (nonl ·s nonr) (one ·s-l nin) =
    elimUnusedUsed nonl one ·s-l elimUnusedUnused nonr nin
  elimUnusedUsed (nonl ·s nonr) (nin ·s-r one) =
    elimUnusedUnused nonl nin ·s-r elimUnusedUsed nonr one

  elimUsed : forall {n} {M : BCIs (succ n)} -> os (z≤th n) ∈!s M -> BCIs n
  elimUsed vars = Is
  elimUsed (uni ·s-l non) = Cs ·s elimUsed uni ·s elimUnused non
  elimUsed (non ·s-r uni) = Bs ·s elimUnused non ·s elimUsed uni

  elimUsedEq : forall {n} {M : BCIs (succ n)} (uni : os (z≤th n) ∈!s M) f a ->
                   ⟦ elimUsed uni ⟧ f · a ≈ ⟦ M ⟧ (punchUp a f)
  elimUsedEq vars f a = Ix a
  elimUsedEq (uni ·s-l non) f a =
    trans-≈ (Cxyz _ _ a) (elimUsedEq uni f a ·-cong elimUnusedEq non f a)
  elimUsedEq (non ·s-r uni) f a =
    trans-≈ (Bxyz _ _ a) (elimUnusedEq non f a ·-cong elimUsedEq uni f a)

  elimUsedUnused : forall {n} {M : BCIs (succ n)} (uni : os (z≤th n) ∈!s M)
                       {x} -> o' x ∉s M -> x ∉s elimUsed uni
  elimUsedUnused vars nin = Is
  elimUsedUnused (uni ·s-l non) (ninl ·s ninr) =
    Cs ·s elimUsedUnused uni ninl ·s elimUnusedUnused non ninr
  elimUsedUnused (non ·s-r uni) (ninl ·s ninr) =
    Bs ·s elimUnusedUnused non ninl ·s elimUsedUnused uni ninr

  elimUsedUsed : forall {n} {M : BCIs (succ n)} (uni : os (z≤th n) ∈!s M)
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

  -- UsageMatch must be proven intrinsically so that the induction step at lam works
  toBCIs : forall {n d G} {t : Term n d} -> G |-[ tt ] t -> Sg (BCIs n) \ M -> UsageMatch G M
  toBCIs {G = G} {var x} (var sub)  = vars x , usageMatch
    where
    usageMatch : UsageMatch G (vars x)
    usageMatch y with y ==th? x
    usageMatch .x | yes refl with 1≤th-indexVZip x sub
    ... | a rewrite 1≤th-index-varQCtx {rho = 1#} x with 1≤th-index x G
    usageMatch _ | yes refl | ≤01ω-refl | .1# = vars
    usageMatch _ | yes refl | ω-bot | .ω# = <>
    usageMatch y | no neq with 1≤th-indexVZip y sub
    ... | ay rewrite 1≤th-index-/=-varQCtx neq 1# with 1≤th-index y G
    usageMatch y | no neq | ≤01ω-refl | .0# = vars neq
    usageMatch y | no neq | ω-bot | .ω# = <>
  toBCIs {G = G} (app {Ge = Ge} {Gs} split er sr) with toBCIs er | toBCIs sr
  ... | Me , pe | Ms , ps = Me ·s Ms , usageMatch
    where
    usageMatch : UsageMatch G (Me ·s Ms)
    usageMatch x with 1≤th-indexVZip x split
    ... | a rewrite 1≤th-index-vzip x _+01ω_ Ge Gs with 1≤th-index x G
    usageMatch x | ≤01ω-refl | .(1≤th-index x _ +01ω 1≤th-index x _)
      with 1≤th-index x Ge | 1≤th-index x Gs | pe x | ps x
    usageMatch x | ≤01ω-refl | .(1≤th-index x Ge +01ω 1≤th-index x Gs) | 0# | 0# | pex | psx = pex ·s psx
    usageMatch x | ≤01ω-refl | .(1≤th-index x Ge +01ω 1≤th-index x Gs) | 0# | 1# | pex | psx = pex ·s-r psx
    usageMatch x | ≤01ω-refl | .(1≤th-index x Ge +01ω 1≤th-index x Gs) | 0# | ω# | pex | psx = <>
    usageMatch x | ≤01ω-refl | .(1≤th-index x Ge +01ω 1≤th-index x Gs) | 1# | 0# | pex | psx = pex ·s-l psx
    usageMatch x | ≤01ω-refl | .(1≤th-index x Ge +01ω 1≤th-index x Gs) | 1# | 1# | pex | psx = <>
    usageMatch x | ≤01ω-refl | .(1≤th-index x Ge +01ω 1≤th-index x Gs) | 1# | ω# | pex | psx = <>
    usageMatch x | ≤01ω-refl | .(1≤th-index x Ge +01ω 1≤th-index x Gs) | ω# | _ | pex | psx = <>
    usageMatch x | ω-bot | .ω# = <>
  toBCIs (the sr) = toBCIs sr
  toBCIs {G = G} (lam sr) with toBCIs sr
  ... | M , p = elimUsed {M = M} (p (os (z≤th _))) , usageMatch
    where
    usageMatch : UsageMatch G (elimUsed (p (os (z≤th _))))
    usageMatch x with 1≤th-index x G | p (o' x)
    usageMatch x | 0# | po'x = elimUsedUnused (p (os (z≤th _))) po'x
    usageMatch x | 1# | po'x = elimUsedUsed (p (os (z≤th _))) po'x
    usageMatch x | ω# | po'x = <>
  toBCIs [ er ] = toBCIs er

  toBCI : forall {n d G} {t : Term n d} -> G |-[ tt ] t -> (1 ≤th n -> A) -> A
  toBCI tr f = ⟦ fst (toBCIs tr) ⟧ f


  -- Semantics

  OneS : Setoid _ _
  OneS = record
    { C = One
    ; setoidOver = record
      { _≈_ = \ _ _ -> One
      ; isSetoid = record
        { refl = <>
        ; sym = λ _ → <>
        ; trans = λ _ _ → <>
        }
      }
    }

  [[_]]T : QTy -> Setoid _ _
  [[ BASE ]]T = OneS
  [[ S ~> T ]]T = PiS [[ S ]]T (unindexed [[ T ]]T)

  [[_]]D : forall {n} -> Ctx n -> Setoid lzero lzero
  [[ nil ]]D = OneS
  [[ T :: D ]]D = SgS [[ T ]]T (unindexed [[ D ]]D)

  [[_]]et : forall {n e T} {D : Ctx n} -> D |- e ∈ T ->
           Setoid.C (PiS [[ D ]]D (unindexed [[ T ]]T))
  [[_]]st : forall {n s T} {D : Ctx n} -> D |- T ∋ s ->
           Setoid.C (PiS [[ D ]]D (unindexed [[ T ]]T))

  [[ var {th} ]]et = go th
    where
    go : forall {n D} (th : 1 ≤th n) -> PiE [[ D ]]D (unindexed [[ 1≤th-index th D ]]T)
    go {D = T :: D} (os th) = record
      { _$E_ = \ { (t , d) -> t }
      ; _$E=_ = \ { (teq , deq) -> teq }
      }
    go {D = T :: D} (o' th) = record
      { _$E_ = \ { (t , d) -> go th $E d }
      ; _$E=_ = \ { (teq , deq) -> go th $E= deq }
      }
  [[ app et st ]]et = record
    { _$E_ = \ d -> ([[ et ]]et $E d) $E ([[ st ]]st $E d)
    ; _$E=_ = \ deq -> ([[ et ]]et $E= deq) ([[ st ]]st $E= deq)
    }
  [[ the st ]]et = [[ st ]]st
  [[_]]st {D = D} (lam st) = record
    { _$E_ = \ d -> record
      { _$E_ = \ s -> [[ st ]]st $E (s , d)
      ; _$E=_ = \ seq -> [[ st ]]st $E= (seq , Setoid.refl [[ D ]]D)
      }
    ; _$E=_ = \ deq seq -> [[ st ]]st $E= (seq , deq)
    }
  [[ [ et ] ]]st = [[ et ]]et

  _,A_ : A -> A -> A
  a ,A b = C · (C · I · a) · b

  --record AssemblyOver {g} r (G : Set g) : Set (a ⊔ g ⊔ lsuc r) where
  --  field
  --    _|=_ : A -> G -> Set r
  --    realiser : G -> A
  --    realises : forall {g} -> realiser g |= g

  --record Assembly g r : Set (a ⊔ lsuc (g ⊔ r)) where
  --  field
  --    [|_|] : Set g
  --    assemblyOver : AssemblyOver r [|_|]
  --  open AssemblyOver assemblyOver renaming (_|=_ to [_]_|=_) public

  --open Assembly public

  --record _=A>_ {g r} (G0 G1 : Assembly g r) : Set (a ⊔ g ⊔ r) where
  --  field
  --    f : [| G0 |] -> [| G1 |]
  --    af : A
  --    realises : forall {g ag} -> [ G0 ] ag |= g -> [ G1 ] af · ag |= f g

module WithBCI! {a l} (S : Setoid a l) (Alg : BCI! S) where
  open Setoid S renaming (C to A; refl to refl-≈; sym to sym-≈; trans to trans-≈)
  open BCI! Alg
  open WithBCI S bci

  --qTyAssembly : QTy -> 01ω -> Assembly _ _
  --qTyAssembly T 0# = record
  --  { [|_|] = {!One!}
  --  ; assemblyOver = {!!}
  --  }
  --qTyAssembly T 1# = {![[ T ]]T!}
  --qTyAssembly T ω# = {!!}

  --qCtxAssembly : forall {n} -> Ctx n -> QCtx n -> Assembly _ _
  --qCtxAssembly nil nil = record
  --  { [|_|] = One
  --  ; assemblyOver = record
  --    { _|=_ = \ _ _ -> One
  --    ; realiser = \ _ -> I
  --    ; realises = <>
  --    }
  --  }
  --qCtxAssembly (T :: D) (rho :: G) = {!rho!}

  --substAssembly : SubstRes vf (replicateVec n tt) G0 G1 -> G0 

  realises : (T : QTy) ->
             Setoid.C (PiS S (unindexed (PiS [[ T ]]T (unindexed (==-Setoid (Set a))))))
  realises BASE = record
    { _$E_ = \ a -> record
      { _$E_ = \ _ -> Lift One
      ; _$E=_ = \ _ -> refl
      }
    ; _$E=_ = \ _ _ -> refl
    }
  realises (S ~> T) = record
    { _$E_ = \ a -> record
      { _$E_ = \ f -> Sg A \ af -> forall {as s} -> realises S $E as $E s ->
                                        Sg _ \ t -> realises T $E (af · as) $E t
      ; _$E=_ = {!\ feq -> ?!}
      }
    ; _$E=_ = {!!}
    }
