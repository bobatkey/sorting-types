module Setoid where

open import Base renaming (refl to ==-refl; sym to ==-sym; trans to ==-trans)
open import Level

record IsSetoid {c l} {C : Set c} (_≈_ : C -> C -> Set l) : Set (c ⊔ l) where
  field
    refl : ∀ {x} -> x ≈ x
    sym : ∀ {x y} -> x ≈ y -> y ≈ x
    trans : ∀ {x y z} -> x ≈ y -> y ≈ z -> x ≈ z

record SetoidOver {c} (C : Set c) l : Set (c ⊔ suc l) where
  infix 4 _≈_
  field
    _≈_ : C -> C -> Set l
    isSetoid : IsSetoid _≈_

  open IsSetoid isSetoid public

record Setoid c l : Set (suc (c ⊔ l)) where
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
       : Set (i ⊔ c ⊔ suc l) where
  infix 4 _≈_
  field
    _≈_ : forall {i j} -> C i -> C j -> Set l
    isSetoidI : IsSetoidI C _≈_

  open IsSetoidI isSetoidI public

record SetoidI {i} (I : Set i) c l : Set (i ⊔ suc (c ⊔ l)) where
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
  infixl 5 _$E_
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

_oE_ : forall {a b c l m n}
       {A : Setoid a l} {B : Setoid b m} {C : Setoid c n} ->
       PiE B (unindexed C) -> PiE A (unindexed B) -> PiE A (unindexed C)
g oE f = record
  { _$E_ = \ x -> g $E (f $E x)
  ; _$E=_ = \ xy -> g $E= (f $E= xy)
  }

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

Subsetoid : forall {a p l X} (A : SetoidOver {a} X l) (P : X -> Set p) ->
            Setoid _ _
Subsetoid A P =
  SgS (record { setoidOver = A })
      (record
        { C = P
        ; setoidIOver = record
          { _≈_ = \ _ _ -> One
          ; isSetoidI = record { refl = <>
                               ; sym = λ _ → <>
                               ; trans = λ _ _ → <>
                               }
          }
        })
