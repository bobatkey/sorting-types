open import Setoid as Setoid'

module FunctionProperties {c l} (S : Setoid c l) where

open import Base renaming (_*_ to _×_)

open Setoid S

Op2 : Set _
Op2 = C → C → C

Rel : (l' : Level) → Set _
Rel l' = C → C → Set l'

--------------------------------------------------------------------------------
-- Operation properties

Cong2 : Op2 → Set _
Cong2 _·_ = ∀ {x x' y y'} → x ≈ x' → y ≈ y' → (x · y) ≈ (x' · y')

IdentityLeft : Op2 → C → Set _
IdentityLeft _·_ e = ∀ x → (e · x) ≈ x

IdentityRight : Op2 → C → Set _
IdentityRight _·_ e = ∀ x → (x · e) ≈ x

Identity : Op2 → C → Set _
Identity _·_ e = IdentityLeft _·_ e × IdentityRight _·_ e

Assoc : Op2 → Set _
Assoc _·_ = ∀ x y z → ((x · y) · z) ≈ (x · (y · z))

Comm : Op2 → Set _
Comm _·_ = ∀ x y → (x · y) ≈ (y · x)

AnnihilLeft : Op2 → C → Set _
AnnihilLeft _·_ z = ∀ x → (z · x) ≈ z

AnnihilRight : Op2 → C → Set _
AnnihilRight _·_ z = ∀ x → (x · z) ≈ z

Annihil : Op2 → C → Set _
Annihil _·_ z = AnnihilLeft _·_ z × AnnihilRight _·_ z

DistribLeft : Op2 → Op2 → Set _
DistribLeft _*_ _+_ = ∀ x y z → (x * (y + z)) ≈ ((x * y) + (x * z))

DistribRight : Op2 → Op2 → Set _
DistribRight _*_ _+_ = ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))

Distrib : Op2 → Op2 → Set _
Distrib _*_ _+_ = DistribLeft _*_ _+_ × DistribRight _*_ _+_

Mono : ∀ {l'} → Rel l' → Op2 → Set _
Mono _≤_ _·_ = ∀ {x x' y y'} → x ≤ x' → y ≤ y' → (x · y) ≤ (x' · y')
