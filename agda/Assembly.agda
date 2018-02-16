open import Setoid as Setoid'
open import BCI as BCI'

module Assembly {a l} {S : Setoid a l} (Alg : BCI S) where

open import Common hiding (_==_; refl; sym; trans) renaming (_*_ to _×_)
open import Category as Category'

open Setoid S renaming (C to A)
open BCI Alg

record Assembly c e r : Set (lsuc (c ⊔ e ⊔ r) ⊔ a ⊔ l) where
  infix 3 _|=_
  field
    U : Setoid c e
    _|=_ : A -> Setoid.C U -> Set r
    realised : forall u -> Sg A \ a -> a |= u
    |=-resp : forall {a a' u u'} -> a ≈ a' -> Setoid._≈_ U u u' -> a |= u -> a' |= u'

  open Setoid U public

ArrA : forall {c e r c' e' r'}
       (B : Assembly c e r) (C : Assembly c' e' r') -> Setoid _ _
ArrA B C =
  Subsetoid (Setoid.setoidOver (B.U ->S C.U))
            \ f -> Sg A \ af -> forall {u au} ->       au  B.|=       u ->
                                                 (af · au) C.|= (f $E u)
  where
  module B = Assembly B ; module C = Assembly C

ASSEMBLY : forall c e r -> Category _ _ _
ASSEMBLY c e r = record
  { Obj = Assembly c e r
  ; Arr = ArrA
  ; isCategory = record
    { id = \ B -> let module B = Assembly B in
                  (record { _$E_ = id ; _$E=_ = id })
                  , I , B.|=-resp (sym (Ix _)) B.refl
    ; _>>_ = \ {A} {B} {C} -> _>>_ {A} {B} {C}
    ; id->> = \ { (g , _) -> (\ xy -> g $E= xy) , <> }
    ; >>-id = \ { (f , _) -> (\ xy -> f $E= xy) , <> }
    ; >>->> = \ { (f , _) (g , _) (h , _) ->
                (\ xy -> h $E= (g $E= (f $E= xy))) , <> }
    }
  }
  where
  module => {B C : Assembly c e r} = Setoid (ArrA B C)

  _>>_ : {A B C : Assembly c e r} ->
         Setoid.C (ArrA A B) -> Setoid.C (ArrA B C) -> Setoid.C (ArrA A C)
  _>>_ {C = C} (f , af , rf) (g , ag , rg) =
    g oE f , B · ag · af
    , λ {u} {au} r ->
      Assembly.|=-resp C (sym (Bxyz ag af au)) (Assembly.refl C) (rg (rf r))

_=A>_ : forall {c e r c' e' r'}
         (B : Assembly c e r) (C : Assembly c' e' r') -> Set _
B =A> C = Setoid.C (ArrA B C)

-- pseudo-record, because _=A>_ is the result of Setoid combinators
module _=A>_ {c e r c' e' r'} {B : Assembly c e r} {C : Assembly c' e' r'}
             (arr : B =A> C) where
  private
    module B = Assembly B
    module C = Assembly C

  f : B.U ->E C.U
  f = fst arr

  af : A
  af = fst (snd arr)

  realises : forall {u au} -> au B.|= u -> af · au C.|= f $E u
  realises = snd (snd arr)

-- combinators on assemblies

open BCI-Combinators _ Alg

oneA : Assembly lzero lzero l
oneA = record
  { U = OneS
  ; _|=_ = \ a _ -> a ≈ I
  ; realised = \ _ -> I , refl
  ; |=-resp = \ aq _ r -> trans (sym aq) r
  }

pairA : forall {c e r c' e' r'} (B : Assembly c e r) (C : Assembly c' e' r') ->
        Assembly (c ⊔ c') (e ⊔ e') (a ⊔ l ⊔ r ⊔ r')
pairA B C = record
  { U = U
  ; _|=_ = _|=_
  ; realised = realised
  ; |=-resp = |=-resp
  }
  where
  module B = Assembly B ; module C = Assembly C

  U = B.U ×S C.U
  open Setoid U using () renaming (C to ∣U∣; _≈_ to _≈U_)

  _|=_ : A -> ∣U∣ -> Set _
  a |= (u , v) = Sg _ \ au -> Sg _ \ av -> a ≈ au ,C av × au B.|= u × av C.|= v

  realised : forall u -> Sg _ \ a -> a |= u
  realised (u , v) = let au , ru = B.realised u in
                     let av , rv = C.realised v in
                     au ,C av , au , av , refl , ru , rv

  |=-resp : forall {a a' u u'} -> a ≈ a' -> u ≈U u' -> a |= u -> a' |= u'
  |=-resp aq (uq , vq) (au , av , split , ru , rv) =
    au , av , trans (sym aq) split , B.|=-resp refl uq ru , C.|=-resp refl vq rv

mapPairA : forall {cb cb' cc cc' eb eb' ec ec' rb rb' rc rc'}
           {B : Assembly cb eb rb} {B' : Assembly cb' eb' rb'}
           {C : Assembly cc ec rc} {C' : Assembly cc' ec' rc'} ->
           B =A> B' -> C =A> C' -> pairA B C =A> pairA B' C'
mapPairA {B' = B'} {C' = C'} (f , af , rf) (g , ag , rg) =
  map×S f g , pmC · (C · (B · B · (B · pairC · af)) · ag)
  , \ { {v , w} {au} (av , aw , auq , rv , rw) ->
      af · av , ag · aw
      , pmC · (C · (B · B · (B · pairC · af)) · ag) · au
          ≈[ refl ·-cong auq ]≈
        pmC · (C · (B · B · (B · pairC · af)) · ag) · (av ,C aw)
          ≈[ pmC-comp _ _ _ ]≈
        C · (B · B · (B · pairC · af)) · ag · av · aw
          ≈[ Cxyz _ _ _ ·-cong refl ]≈
        B · B · (B · pairC · af) · av · ag · aw
          ≈[ Bxyz _ _ _ ·-cong refl ·-cong refl ]≈
        B · (B · pairC · af · av) · ag · aw
          ≈[ refl ·-cong Bxyz _ _ _ ·-cong refl ·-cong refl ]≈
        B · (pairC · (af · av)) · ag · aw
          ≈[ Bxyz _ _ _ ]≈
        pairC · (af · av) · (ag · aw)
          ≈[ pairC-comp _ _ ]≈
        af · av ,C ag · aw
          QED
      , rf rv , rg rw
      }
  where
  open Assembly (pairA B' C') using (|=-resp)
  open SetoidReasoning S

_->A_ : forall {c e r c' e' r'}
        (B : Assembly c e r) (C : Assembly c' e' r') -> Assembly _ _ _
B ->A C = record
  { U = U
  ; _|=_ = _|=_
  ; realised = realised
  ; |=-resp = \ {a} {a'} {u} {u'} -> |=-resp {a} {a'} {u} {u'}
  }
  where
  module B = Assembly B ; module C = Assembly C

  U = ArrA B C
  open Setoid U using () renaming (C to ∣U∣; _≈_ to _≈U_)

  _|=_ : A -> ∣U∣ -> Set _
  a |= (f , af , rf) = forall {x ax} -> ax B.|= x -> af · ax C.|= f $E x

  realised : forall u -> Sg _ \ a -> a |= u
  realised (f , af , rf) = af , rf

  |=-resp : forall {a a' u u'} -> a ≈ a' -> u ≈U u' -> a |= u -> a' |= u'
  |=-resp {a} {a'} {uf , af , rf} {uf' , af' , rf'} aq (fq , <>) r rx = rf' rx

pmA : forall {cb eb rb cc ec rc cd ed rd}
      {B : Assembly cb eb rb} {C : Assembly cc ec rc} {D : Assembly cd ed rd} ->
      B =A> (C ->A D) -> pairA B C =A> D
pmA {D = D} (f , af , rf) =
  pmS (record { _$E_ = \ b -> fst (f $E b)
              ; _$E=_ = \ {b} {b'} bq {c} {c'} cq -> fst (f $E= bq) cq
              })
  , pmC · af
  , \ { {b , c} {au} (ab , ac , auq , rb , rc) ->
      |=-resp
        (sym (pmC · af · au  ≈[ {!!} ]≈
              pmC · af · (ab ,C ac)  ≈[ {!!} ]≈
              af · ab · ac  ≈[ {!!} ]≈
              fst (snd (f $E b)) · ac  QED))
        {!!}
        (rf rb rc)
      }
  where
  open Assembly D using (|=-resp)
  open SetoidReasoning S

LiftA : forall {c e r c' e' r'} ->
        Assembly c e r -> Assembly (c ⊔ c') (e ⊔ e') (r ⊔ r')
LiftA {c' = c'} {e'} {r'} B = record
  { U = LiftS {a' = c'} {e'} U
  ; _|=_ = \ { a (lift u) → Lift {l = r'} (a |= u) }
  ; realised = \ { (lift u) -> mapSg id lift (realised u) }
  ; |=-resp = \ { aq (lift uq) (lift r) -> lift (|=-resp aq uq r) }
  }
  where open Assembly B
