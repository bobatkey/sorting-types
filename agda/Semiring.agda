module Semiring where

open import Common using (_*_)
open import Level

Op2 : ∀ {x} → Set x → Set x
Op2 X = X → X → X

Rel : ∀ {c} → Set c → (l : Level) → Set (c ⊔ suc l)
Rel C l = C → C → Set l

-- Relation properties

Refl : ∀ {c l} {C : Set c} → Rel C l → Set (c ⊔ l)
Refl _~_ = ∀ {x} → x ~ x

Sym : ∀ {c l} {C : Set c} → Rel C l → Set (c ⊔ l)
Sym _~_ = ∀ {x y} → x ~ y → y ~ x

Trans : ∀ {c l} {C : Set c} → Rel C l → Set (c ⊔ l)
Trans _~_ = ∀ {x y z} → x ~ y → y ~ z → x ~ z

module FunctionProperties {c l} {C : Set c} (_≈_ : Rel C l) where
  Reflexive : ∀ {l'} → Rel C l' → Set (c ⊔ l ⊔ l')
  Reflexive _≤_ = ∀ {x y} → x ≈ y → x ≤ y

  Cong2 : Op2 C → Set _
  Cong2 _·_ = ∀ {x x' y y'} → x ≈ x' → y ≈ y' → (x · y) ≈ (x' · y')

  Identity : Op2 C → C → Set _
  Identity _·_ e = ∀ {x} → ((e · x) ≈ x) * ((x · e) ≈ x)

  Assoc : Op2 C → Set _
  Assoc _·_ = ∀ {x y z} → ((x · y) · z) ≈ (x · (y · z))

  Comm : Op2 C → Set _
  Comm _·_ = ∀ {x y} → (x · y) ≈ (y · x)

-- Structures

record IsSetoid {c l} {C : Set c} (≈ : Rel C l) : Set (c ⊔ l) where
  field
    refl : Refl ≈
    sym : Sym ≈
    trans : Trans ≈

record IsPoset {c l l'} {C : Set c} (≈ : Rel C l) (≤ : Rel C l') : Set (c ⊔ l ⊔ l') where
  open FunctionProperties ≈
  field
    isSetoid : IsSetoid ≈
    reflexive : Reflexive ≤
    trans : Trans ≤

record PosetOver {c} (C : Set c) l l' : Set (c ⊔ suc (l ⊔ l')) where
  field
    ≈ : Rel C l
    ≤ : Rel C l'
    isPoset : IsPoset ≈ ≤

record IsMonoid {c l} {C : Set c} (≈ : Rel C l) (e : C) (· : Op2 C) : Set (c ⊔ l) where
  open FunctionProperties ≈
  field
    isSetoid : IsSetoid ≈
    identity : Identity · e
    assoc : Assoc ·
    _·-cong_ : Cong2 ·

record MonoidOver {c} (C : Set c) l : Set (c ⊔ suc l) where
  field
    ≈ : Rel C l
    e : C
    · : Op2 C
    isMonoid : IsMonoid ≈ e ·

record Monoid {c l} : Set (suc (c ⊔ l)) where
  field
    C : Set c
    monoidOver : MonoidOver C l

record IsCommutativeMonoid {c l} {C : Set c} (≈ : Rel C l) (e : C) (· : Op2 C) : Set (c ⊔ l) where
  open FunctionProperties ≈
  field
    comm : Comm ·
    isMonoid : IsMonoid ≈ e ·

record CommutativeMonoidOver {c} (C : Set c) l : Set (c ⊔ suc l) where
  field
    ≈ : Rel C l
    e : C
    · : Op2 C
    isCommutativeMonoid : IsCommutativeMonoid ≈ e ·

--record
