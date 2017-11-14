open import Setoid as Setoid'

module Structure {c l} (S : Setoid c l) where

open import Base hiding (refl) renaming (_*_ to _×_)
open import FunctionProperties S

open Setoid S

--------------------------------------------------------------------------------
-- Relation properties

Refl : ∀ {l'} → Rel l' → Set _
Refl _~_ = ∀ {x} → x ~ x

Sym : ∀ {l'} → Rel l' → Set _
Sym _~_ = ∀ {x y} → x ~ y → y ~ x

Trans : ∀ {l'} → Rel l' → Set _
Trans _~_ = ∀ {x y z} → x ~ y → y ~ z → x ~ z

Reflexive : ∀ {l'} → Rel l' → Set _
Reflexive _≤_ = ∀ {x y} → x ≈ y → x ≤ y

Antisym : ∀ {l'} → Rel l' → Set _
Antisym _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

--------------------------------------------------------------------------------
-- Structures

record IsPreorder {l'} (≤ : Rel l') : Set (c ⊔ l ⊔ l') where
  field
    ≤-reflexive : Reflexive ≤
    ≤-trans : Trans ≤
  ≤-refl : Refl ≤
  ≤-refl = ≤-reflexive refl

record Preorder l' : Set (c ⊔ l ⊔ lsuc l') where
  field
    _≤_ : Rel l'
    isPreorder : IsPreorder _≤_
  open IsPreorder isPreorder public

record IsPoset {l'} (≤ : Rel l') : Set (c ⊔ l ⊔ l') where
  field
    antisym : Antisym ≤
    isPreorder : IsPreorder ≤
  open IsPreorder isPreorder public

record Poset l' : Set (c ⊔ l ⊔ lsuc l') where
  field
    _≤_ : Rel l'
    isPoset : IsPoset _≤_
  open IsPoset isPoset public

record IsMeetSemilattice {l'} (_≤_ : Rel l') (meet : Op2) : Set (c ⊔ l ⊔ l') where
  field
    lowerBound : (forall a b -> meet a b ≤ a) × (forall a b -> meet a b ≤ b)
    greatest : forall {a b m} -> m ≤ a -> m ≤ b -> m ≤ meet a b
    isPoset : IsPoset _≤_
  open IsPoset isPoset public

record MeetSemilattice l' : Set (c ⊔ l ⊔ lsuc l') where
  field
    _≤_ : Rel l'
    meet : Op2
    isMeetSemilattice : IsMeetSemilattice _≤_ meet
  open IsMeetSemilattice isMeetSemilattice public

record IsLattice {l'} (_≤_ : Rel l') (meet join : Op2) : Set (c ⊔ l ⊔ l') where
  field
    lowerBound : (forall a b -> meet a b ≤ a) × (forall a b -> meet a b ≤ b)
    upperBound : (forall a b -> a ≤ join a b) × (forall a b -> b ≤ join a b)
    greatest : forall {a b m} -> m ≤ a -> m ≤ b -> m ≤ meet a b
    least : forall {a b m} -> a ≤ m -> b ≤ m -> join a b ≤ m
    isPoset : IsPoset _≤_
  open IsPoset isPoset public

record Lattice l' : Set (c ⊔ l ⊔ lsuc l') where
  field
    _≤_ : Rel l'
    meet join : Op2
    isLattice : IsLattice _≤_ meet join
  open IsLattice isLattice public

  meetSemilattice : MeetSemilattice l'
  meetSemilattice = record { isMeetSemilattice = record { lowerBound = lowerBound
                                                        ; greatest = greatest
                                                        ; isPoset = isPoset
                                                        } }
  open MeetSemilattice meetSemilattice public
    using (isMeetSemilattice)

--

record IsMonoid (e : C) (· : Op2) : Set (c ⊔ l) where
  field
    identity : Identity · e
    assoc : Assoc ·
    _·-cong_ : Cong2 ·

record Monoid : Set (c ⊔ l) where
  field
    e : C
    _·_ : Op2
    isMonoid : IsMonoid e _·_
  open IsMonoid isMonoid public

record IsCommutativeMonoid (e : C) (· : Op2) : Set (c ⊔ l) where
  field
    comm : Comm ·
    isMonoid : IsMonoid e ·
  open IsMonoid isMonoid public

record CommutativeMonoid : Set (c ⊔ l) where
  field
    e : C
    _·_ : Op2
    isCommutativeMonoid : IsCommutativeMonoid e _·_
  open IsCommutativeMonoid isCommutativeMonoid public

  monoid : Monoid
  monoid = record { isMonoid = isMonoid }

record IsSemiring (e0 e1 : C) (+ * : Op2) : Set (c ⊔ l) where
  field
    +-isCommutativeMonoid : IsCommutativeMonoid e0 +
    *-isMonoid : IsMonoid e1 *
    annihil : Annihil * e0
    distrib : Distrib * +
  open IsCommutativeMonoid +-isCommutativeMonoid public
    renaming (comm to +-comm; isMonoid to +-isMonoid;
              identity to +-identity; assoc to +-assoc; _·-cong_ to _+-cong_)
  open IsMonoid *-isMonoid public
    renaming (identity to *-identity; assoc to *-assoc; _·-cong_ to _*-cong_)

record Semiring : Set (c ⊔ l) where
  field
    e0 e1 : C
    _+_ _*_ : Op2
    isSemiring : IsSemiring e0 e1 _+_ _*_
  open IsSemiring isSemiring public

  +-commutativeMonoid : CommutativeMonoid
  +-commutativeMonoid = record { isCommutativeMonoid = +-isCommutativeMonoid }
  open CommutativeMonoid +-commutativeMonoid public
    using ()
    renaming (monoid to +-monoid)

  *-monoid : Monoid
  *-monoid = record { isMonoid = *-isMonoid }

record IsPosemiring {l'} (≤ : Rel l') (e0 e1 : C) (+ * : Op2) : Set (c ⊔ l ⊔ l') where
  field
    _+-mono_ : Mono ≤ +
    _*-mono_ : Mono ≤ *
    isPoset : IsPoset ≤
    isSemiring : IsSemiring e0 e1 + *
  open IsPoset isPoset public
  open IsSemiring isSemiring public

record Posemiring l' : Set (c ⊔ l ⊔ lsuc l') where
  field
    _≤_ : Rel l'
    e0 e1 : C
    _+_ _*_ : Op2
    isPosemiring : IsPosemiring _≤_ e0 e1 _+_ _*_
  open IsPosemiring isPosemiring public

  poset : Poset l'
  poset = record { isPoset = isPoset }

  semiring : Semiring
  semiring = record { isSemiring = isSemiring }
  open Semiring semiring public
    using (+-monoid; +-commutativeMonoid; *-monoid)

record IsMeetSemilatticeSemiring {l'} (≤ : Rel l') (e0 e1 : C) (+ * meet : Op2)
                                 : Set (c ⊔ l ⊔ l') where
  field
    _+-mono_ : Mono ≤ +
    _*-mono_ : Mono ≤ *
    isMeetSemilattice : IsMeetSemilattice ≤ meet
    isSemiring : IsSemiring e0 e1 + *
  open IsMeetSemilattice isMeetSemilattice public
  open IsSemiring isSemiring public

record MeetSemilatticeSemiring l' : Set (c ⊔ l ⊔ lsuc l') where
  field
    _≤_ : Rel l'
    e0 e1 : C
    _+_ _*_ meet : Op2
    isMeetSemilatticeSemiring : IsMeetSemilatticeSemiring _≤_ e0 e1 _+_ _*_ meet
  open IsMeetSemilatticeSemiring isMeetSemilatticeSemiring public

  meetSemilattice : MeetSemilattice l'
  meetSemilattice = record { isMeetSemilattice = isMeetSemilattice }
