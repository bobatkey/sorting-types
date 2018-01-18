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
      Setoid (Arr A B) using (_≈_; refl; sym; trans)

    open IsCategory isCategory public
