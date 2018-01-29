module Category where

  open import Common using (_⊔_; lsuc)
  open import Setoid as Setoid'

  record IsCategory {o a e} {Obj : Set o} (Arr : (A B : Obj) -> Setoid a e)
                    : Set (o ⊔ a ⊔ e) where
    open module Arr (A B : Obj) =
      Setoid (Arr A B) renaming (C to _=>_; _≈_ to [_,_]_≈_)
    infixr 5 _>>_
    field
      id : (A : Obj) -> A => A
      _>>_ : {A B C : Obj} -> A => B -> B => C -> A => C

      id->> : forall {A B} (g : A => B) -> [ A , B ] id A >> g ≈ g
      >>-id : forall {A B} (f : A => B) -> [ A , B ] f >> id B ≈ f
      >>->> : forall {A B C D} (f : A => B) (g : B => C) (h : C => D) ->
              [ A , D ] (f >> g) >> h ≈ f >> (g >> h)

  record Category o a e : Set (lsuc (o ⊔ a ⊔ e)) where
    infixr 4 _=>_
    field
      Obj : Set o
      Arr : (A B : Obj) -> Setoid a e
      isCategory : IsCategory Arr

    _=>_ : (A B : Obj) -> Set a
    A => B = let open Setoid (Arr A B) in C
    open module Dummy {A B : Obj} =
      Setoid (Arr A B) using (_≈_; refl; sym; trans) public

    open IsCategory isCategory public

  SETOID : forall c l -> Category _ _ _
  SETOID c l = record
    { Obj = Setoid c l
    ; Arr = _->S_
    ; isCategory = record
      { id = idE
      ; _>>_ = _>>E_
      ; id->> = id->>
      ; >>-id = >>-id
      ; >>->> = >>->>
      }
    }
    where
    module _ {A B : Setoid c l} where
      open Setoid (A ->S B)

      id->> : forall g -> idE A >>E g ≈ g
      id->> g aq = g $E= aq

      >>-id : forall f -> f >>E idE B ≈ f
      >>-id f aq = f $E= aq

    module _ {A B C D : Setoid c l} where
      open Setoid (A ->S D) using (_≈_)

      >>->> : (f : A ->E B) (g : B ->E C) (h : C ->E D) ->
              (f >>E g) >>E h ≈ f >>E (g >>E h)
      >>->> f g h aq = h $E= (g $E= (f $E= aq))

  module _ {o a e} (C D : Category o a e) where
    private
      module C = Category C ; module D = Category D
    open D using (_≈_)

    record IsFunctor (fobj : C.Obj -> D.Obj) (farr : forall {A B} -> C.Arr A B ->E D.Arr (fobj A) (fobj B)) : Set (o ⊔ a ⊔ e) where
      field
        farr-id : forall A -> farr $E (C.id A) ≈ D.id (fobj A)
        farr->> : forall {A B C} {f : A C.=> B} {g : B C.=> C} ->
                  farr $E (f C.>> g) ≈ farr $E f D.>> farr $E g

  record Functor {o a e} (C D : Category o a e) : Set (o ⊔ a ⊔ e) where
    private
      module C = Category C ; module D = Category D
    field
      fobj : C.Obj -> D.Obj
      farr : forall {A B} -> C.Arr A B ->E D.Arr (fobj A) (fobj B)
      isFunctor : IsFunctor C D fobj farr

  {-+}
  CATEGORY : forall o a e -> Category _ _ _
  CATEGORY o a e = record
    { Obj = Category o a e
    ; Arr = {!Functor!}
    ; isCategory = {!!}
    }
  {+-}
