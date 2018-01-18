open import Setoid as Setoid'
open import BCI as BCI'

module Assembly {a l} {S : Setoid a l} (Alg : BCI S) where

open import Common hiding (_==_; refl; sym; trans)
open import Category as Category'

open Setoid S renaming (C to A)
open BCI Alg

record Assembly c e r : Set (lsuc (c ⊔ e ⊔ r) ⊔ a ⊔ l) where
  field
    U : Setoid c e
    _|=_ : A -> Setoid.C U -> Set r
    realised : forall u -> Sg A \ a -> a |= u
    |=-resp : forall {a a' u u'} -> a ≈ a' -> Setoid._≈_ U u u' -> a |= u -> a' |= u'

  open Setoid U public

record _=A>_ {c e r} (B C : Assembly c e r) : Set (lsuc (c ⊔ e ⊔ r) ⊔ a) where
  private
    module B = Assembly B
    module C = Assembly C
  field
    f : PiE B.U (unindexed C.U)
    af : A
    realises : forall {u au} -> au B.|= u -> (af · au) C.|= (f $E u)

ArrA : forall {c e r} (B C : Assembly c e r) -> Setoid _ _
ArrA B C =
  Subsetoid (Setoid.setoidOver (PiS B.U (unindexed C.U)))
            \ f → Sg A \ af -> forall {u au} ->       au  B.|=       u ->
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
