module Setoid where

open import Base renaming (refl to ==-refl; sym to ==-sym; trans to ==-trans)
open import Level

record IsSetoid {c l} {C : Set c} (_≈_ : C → C → Set l) : Set (c ⊔ l) where
  field
    refl : ∀ {x} → x ≈ x
    sym : ∀ {x y} → x ≈ y → y ≈ x
    trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z

record SetoidOver {c} (C : Set c) l : Set (c ⊔ suc l) where
  field
    _≈_ : C → C → Set l
    isSetoid : IsSetoid _≈_

  open IsSetoid isSetoid public

record Setoid c l : Set (suc (c ⊔ l)) where
  field
    C : Set c
    setoidOver : SetoidOver C l

  open SetoidOver setoidOver public

==-SetoidOver : ∀ {x} (X : Set x) -> SetoidOver X x
==-SetoidOver X = record
  { _≈_ = _==_
  ; isSetoid = record { refl = ==-refl ; sym = ==-sym ; trans = ==-trans }
  }

==-Setoid : ∀ {x} -> Set x -> Setoid x x
==-Setoid X = record { C = X ; setoidOver = ==-SetoidOver X }
