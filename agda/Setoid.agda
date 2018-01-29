module Setoid where

open import Base renaming (refl to ==-refl; sym to ==-sym; trans to ==-trans)
open import Common using (Lift; lift; lower)

record IsSetoid {c l} {C : Set c} (_≈_ : C -> C -> Set l) : Set (c ⊔ l) where
  field
    refl : ∀ {x} -> x ≈ x
    sym : ∀ {x y} -> x ≈ y -> y ≈ x
    trans : ∀ {x y z} -> x ≈ y -> y ≈ z -> x ≈ z

record SetoidOver {c} (C : Set c) l : Set (c ⊔ lsuc l) where
  infix 4 _≈_
  field
    _≈_ : C -> C -> Set l
    isSetoid : IsSetoid _≈_

  open IsSetoid isSetoid public

record Setoid c l : Set (lsuc (c ⊔ l)) where
  field
    C : Set c
    setoidOver : SetoidOver C l

  open SetoidOver setoidOver public

==-SetoidOver : forall {x} (X : Set x) -> SetoidOver X x
==-SetoidOver X = record
  { _≈_ = _==_
  ; isSetoid = record { refl = ==-refl ; sym = ==-sym ; trans = ==-trans }
  }

==-Setoid : forall {x} -> Set x -> Setoid x x
==-Setoid X = record { C = X ; setoidOver = ==-SetoidOver X }

-- Indexed setoids

record IsSetoidI {i c l} {I : Set i} (C : I -> Set c)
                 (_≈_ : forall {i j} -> C i -> C j -> Set l)
                 : Set (i ⊔ c ⊔ l) where
  field
    refl : ∀ {i} {x : C i} -> x ≈ x
    sym : ∀ {i j} {x : C i} {y : C j} -> x ≈ y -> y ≈ x
    trans : ∀ {i j k} {x : C i} {y : C j} {z : C k} -> x ≈ y -> y ≈ z -> x ≈ z

record SetoidIOver {i c} {I : Set i} (C : I -> Set c) l
       : Set (i ⊔ c ⊔ lsuc l) where
  infix 4 _≈_
  field
    _≈_ : forall {i j} -> C i -> C j -> Set l
    isSetoidI : IsSetoidI C _≈_

  open IsSetoidI isSetoidI public

record SetoidI {i} (I : Set i) c l : Set (i ⊔ lsuc (c ⊔ l)) where
  field
    C : I -> Set c
    setoidIOver : SetoidIOver C l

  open SetoidIOver setoidIOver public

unindexed : forall {i c l} {I : Set i} -> Setoid c l -> SetoidI I c l
unindexed S = record
  { C = \ _ -> C
  ; setoidIOver = record
    { _≈_ = _≈_
    ; isSetoidI = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    }
  }
  where open Setoid S

-- Functions with extensional equality

record PiE {a b l m} (A : Setoid a l) (B : SetoidI (Setoid.C A) b m)
       : Set (a ⊔ b ⊔ l ⊔ m) where
  private
    module A = Setoid A ; module B = SetoidI B
  infixl 6 _$E_ _$E=_
  field
    _$E_ : (x : A.C) -> B.C x
    _$E=_ : forall {x y} -> x A.≈ y -> _$E_ x B.≈ _$E_ y

open PiE public

PiS : forall {a b l m} (A : Setoid a l) (B : SetoidI (Setoid.C A) b m) -> Setoid _ _
PiS A B = record
  { C = PiE A B
  ; setoidOver = record
    { _≈_ = \ f g -> forall {x y} -> x A.≈ y -> f $E x B.≈ g $E y
    ; isSetoid = record
      { refl = \ {f} xy -> f $E= xy
      ; sym = \ {f} {g} fg xy -> B.sym (fg (A.sym xy))
      ; trans = \ {f} {g} {h} fg gh xy -> B.trans (fg A.refl) (gh xy)
      }
    }
  }
  where module A = Setoid A ; module B = SetoidI B

infixr 3 _->E_ _->S_
_->E_ : forall {a b l m} (A : Setoid a l) (B : Setoid b m) -> Set _
A ->E B = PiE A (unindexed B)

_->S_ : forall {a b l m} (A : Setoid a l) (B : Setoid b m) -> Setoid _ _
A ->S B = PiS A (unindexed B)

idE : forall {a l} (A : Setoid a l) -> A ->E A
idE A = record { _$E_ = \ x -> x ; _$E=_ = \ xq -> xq }

infixr 5 _oE_ _>>E_
_oE_ : forall {a b c l m n}
       {A : Setoid a l} {B : Setoid b m} {C : Setoid c n} ->
       B ->E C -> A ->E B -> A ->E C
g oE f = record
  { _$E_ = \ x -> g $E (f $E x)
  ; _$E=_ = \ xy -> g $E= (f $E= xy)
  }

_>>E_ : forall {a b c l m n}
       {A : Setoid a l} {B : Setoid b m} {C : Setoid c n} ->
       A ->E B -> B ->E C -> A ->E C
f >>E g = g oE f

-- Pairs

SgS : forall {a b l m} (A : Setoid a l) (B : SetoidI (Setoid.C A) b m) ->
                       Setoid _ _
SgS A B = record
  { C = Sg A.C B.C
  ; setoidOver = record
    { _≈_ = \ { (ax , bx) (ay , by) -> Sg (ax A.≈ ay) (\ aeq -> bx B.≈ by) }
    ; isSetoid = record
      { refl = A.refl , B.refl
      ; sym = \ { (axy , bxy) -> A.sym axy , B.sym bxy }
      ; trans = \ { (axy , bxy) (ayz , byz)
                 -> A.trans axy ayz , B.trans bxy byz
                  }
      }
    }
  }
  where module A = Setoid A ; module B = SetoidI B

_×S_ : forall {a b l m} (A : Setoid a l) (B : Setoid b m) -> Setoid _ _
A ×S B = SgS A (unindexed B)

Subsetoid : forall {a p l X} (A : SetoidOver {a} X l) (P : X -> Set p) ->
            Setoid _ _
Subsetoid A P =
  SgS (record { setoidOver = A })
      (record
        { C = P
        ; setoidIOver = record
          { _≈_ = \ _ _ -> One
          ; isSetoidI = record { refl = <>
                               ; sym = \ _ -> <>
                               ; trans = \ _ _ -> <>
                               }
          }
        })

OneS : Setoid lzero lzero
OneS = record
  { C = One
  ; setoidOver = record
    { _≈_ = \ _ _ -> One
    ; isSetoid = record { refl = <> ; sym = \ _ -> <> ; trans = \ _ _ -> <> }
    }
  }

LiftS : forall {a l a' l'} -> Setoid a l -> Setoid (a ⊔ a') (l ⊔ l')
LiftS {a' = a'} {l'} S = record
  { C = Lift {l = a'} C
  ; setoidOver = record
    { _≈_ = \ { (lift x) (lift y) -> Lift {l = l'} (x ≈ y) }
    ; isSetoid = record
      { refl = lift refl
      ; sym = \ { (lift xy) -> lift (sym xy) }
      ; trans = \ { (lift xy) (lift yz) -> lift (trans xy yz) }
      }
    }
  }
  where open Setoid S
