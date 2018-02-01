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

record _=A>_ {c e r c' e' r'} (B : Assembly c e r) (C : Assembly c' e' r')
              : Set (lsuc (c ⊔ e ⊔ r ⊔ c' ⊔ e' ⊔ r') ⊔ a) where
  private
    module B = Assembly B
    module C = Assembly C
  field
    f : B.U ->E C.U
    af : A
    realises : forall {u au} -> au B.|= u -> (af · au) C.|= (f $E u)

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

-- combinators on assemblies

open BCI-Combinators _ Alg

oneA : Assembly lzero lzero l
oneA = record
  { U = OneS
  ; _|=_ = \ a _ -> a ≈ I
  ; realised = \ _ -> I , refl
  ; |=-resp = \ aq _ r -> trans (sym aq) r
  }

pairA : forall {c e r} (B C : Assembly c e r) -> Assembly c e (a ⊔ l ⊔ r)
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

LiftA : forall {c e r c' e' r'} ->
        Assembly c e r -> Assembly (c ⊔ c') (e ⊔ e') (r ⊔ r')
LiftA {c' = c'} {e'} {r'} B = record
  { U = LiftS {a' = c'} {e'} U
  ; _|=_ = \ { a (lift u) → Lift {l = r'} (a |= u) }
  ; realised = \ { (lift u) -> mapSg id lift (realised u) }
  ; |=-resp = \ { aq (lift uq) (lift r) -> lift (|=-resp aq uq r) }
  }
  where open Assembly B
