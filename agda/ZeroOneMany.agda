module ZeroOneMany where

open import Common hiding (_=>_; LTy; KEY; LIST; _<**>_; _&_; _-o_)
                   renaming (_*_ to _×_)
open import Setoid

data 01ω : Set where
  0# 1# ω# : 01ω

01ωSetoid : Setoid lzero lzero
01ωSetoid = ==-Setoid 01ω

open import FunctionProperties 01ωSetoid
open import Structure 01ωSetoid

data _≤01ω_ : Rel lzero where
  ≤01ω-refl : ∀ {x} → x ≤01ω x
  ω-bot : ∀ {x} → ω# ≤01ω x

_+01ω_ : Op2
0# +01ω y = y
1# +01ω 0# = 1#
1# +01ω 1# = ω#
1# +01ω ω# = ω#
ω# +01ω y = ω#

_*01ω_ : Op2
0# *01ω y = 0#
1# *01ω y = y
ω# *01ω 0# = 0#
ω# *01ω 1# = ω#
ω# *01ω ω# = ω#

+01ω-isCommutativeMonoid : IsCommutativeMonoid 0# _+01ω_
+01ω-isCommutativeMonoid = record
  { comm = comm
  ; isMonoid = record
    { identity = (λ y → refl) , identityRight
    ; assoc = assoc
    ; _·-cong_ = cong2 _
    }
  }
  where
  identityRight : IdentityRight _+01ω_ 0#
  identityRight 0# = refl
  identityRight 1# = refl
  identityRight ω# = refl

  assoc : Assoc _+01ω_
  assoc 0# y z = refl
  assoc 1# 0# z = refl
  assoc 1# 1# 0# = refl
  assoc 1# 1# 1# = refl
  assoc 1# 1# ω# = refl
  assoc 1# ω# z = refl
  assoc ω# y z = refl

  comm : Comm _+01ω_
  comm 0# 0# = refl
  comm 0# 1# = refl
  comm 0# ω# = refl
  comm 1# 0# = refl
  comm 1# 1# = refl
  comm 1# ω# = refl
  comm ω# 0# = refl
  comm ω# 1# = refl
  comm ω# ω# = refl

*01ω-isMonoid : IsMonoid 1# _*01ω_
*01ω-isMonoid = record
  { identity = (λ y → refl) , identityRight
  ; assoc = assoc
  ; _·-cong_ = cong2 _
  }
  where
  identityRight : IdentityRight _*01ω_ 1#
  identityRight 0# = refl
  identityRight 1# = refl
  identityRight ω# = refl

  assoc : Assoc _*01ω_
  assoc 0# y z = refl
  assoc 1# y z = refl
  assoc ω# 0# z = refl
  assoc ω# 1# z = refl
  assoc ω# ω# 0# = refl
  assoc ω# ω# 1# = refl
  assoc ω# ω# ω# = refl

01ω-isSemiring : IsSemiring 0# 1# _+01ω_ _*01ω_
01ω-isSemiring = record
  { +-isCommutativeMonoid = +01ω-isCommutativeMonoid
  ; *-isMonoid = *01ω-isMonoid
  ; annihil = (λ y → refl) , annihilRight
  ; distrib = distribLeft , distribRight
  }
  where
  annihilRight : AnnihilRight _*01ω_ 0#
  annihilRight 0# = refl
  annihilRight 1# = refl
  annihilRight ω# = refl

  distribLeft : DistribLeft _*01ω_ _+01ω_
  distribLeft 0# y z = refl
  distribLeft 1# y z = refl
  distribLeft ω# 0# z = refl
  distribLeft ω# 1# 0# = refl
  distribLeft ω# 1# 1# = refl
  distribLeft ω# 1# ω# = refl
  distribLeft ω# ω# z = refl

  distribRight : DistribRight _*01ω_ _+01ω_
  distribRight x 0# z = refl
  distribRight 0# 1# z = trans (annihilRight (1# +01ω z)) (sym (annihilRight z))
  distribRight 1# 1# 0# = refl
  distribRight 1# 1# 1# = refl
  distribRight 1# 1# ω# = refl
  distribRight ω# 1# 0# = refl
  distribRight ω# 1# 1# = refl
  distribRight ω# 1# ω# = refl
  distribRight 0# ω# z = sym (annihilRight z)
  distribRight 1# ω# z = refl
  distribRight ω# ω# z = refl

01ωSemiring : Semiring
01ωSemiring = record
  { e0 = 0#
  ; e1 = 1#
  ; _+_ = _+01ω_
  ; _*_ = _*01ω_
  ; isSemiring = 01ω-isSemiring
  }

≤01ω-trans : ∀ {x y z} → x ≤01ω y → y ≤01ω z → x ≤01ω z
≤01ω-trans ≤01ω-refl yz = yz
≤01ω-trans ω-bot yz = ω-bot

01ω-isPoset : IsPoset _≤01ω_
01ω-isPoset = record
  { antisym = antisym
  ; isPreorder = record
    { ≤-reflexive = λ { refl → ≤01ω-refl }
    ; ≤-trans = ≤01ω-trans
    }
  }
  where
  antisym : Antisym _≤01ω_
  antisym ≤01ω-refl yx = refl
  antisym ω-bot ≤01ω-refl = refl
  antisym ω-bot ω-bot = refl

meet01ω : Op2
meet01ω 0# 0# = 0#
meet01ω 0# 1# = ω#
meet01ω 0# ω# = ω#
meet01ω 1# 0# = ω#
meet01ω 1# 1# = 1#
meet01ω 1# ω# = ω#
meet01ω ω# y = ω#

01ω-isMeetSemilattice : IsMeetSemilattice _≤01ω_ meet01ω
01ω-isMeetSemilattice = record
  { lowerBound = lowerBoundL , lowerBoundR
  ; greatest = greatest
  ; isPoset = 01ω-isPoset
  }
  where
  lowerBoundL : forall x y -> meet01ω x y ≤01ω x
  lowerBoundL 0# 0# = ≤01ω-refl
  lowerBoundL 0# 1# = ω-bot
  lowerBoundL 0# ω# = ω-bot
  lowerBoundL 1# 0# = ω-bot
  lowerBoundL 1# 1# = ≤01ω-refl
  lowerBoundL 1# ω# = ω-bot
  lowerBoundL ω# y = ≤01ω-refl

  lowerBoundR : forall x y -> meet01ω x y ≤01ω y
  lowerBoundR 0# 0# = ≤01ω-refl
  lowerBoundR 0# 1# = ω-bot
  lowerBoundR 0# ω# = ≤01ω-refl
  lowerBoundR 1# 0# = ω-bot
  lowerBoundR 1# 1# = ≤01ω-refl
  lowerBoundR 1# ω# = ≤01ω-refl
  lowerBoundR ω# y = ω-bot

  greatest : ∀ {x y m} → m ≤01ω x → m ≤01ω y → m ≤01ω meet01ω x y
  greatest {0#} {0#} mx my = my
  greatest {0#} {1#} ≤01ω-refl ()
  greatest {0#} {1#} ω-bot my = ≤01ω-refl
  greatest {0#} {ω#} mx my = my
  greatest {1#} {0#} ≤01ω-refl ()
  greatest {1#} {0#} ω-bot my = ≤01ω-refl
  greatest {1#} {1#} mx my = my
  greatest {1#} {ω#} mx my = my
  greatest {ω#} mx my = mx

01ωPosemiring : Posemiring lzero
01ωPosemiring = record
  { _≤_ = _≤01ω_
  ; e0 = 0#
  ; e1 = 1#
  ; _+_ = _+01ω_
  ; _*_ = _*01ω_
  ; isPosemiring = record
    { _+-mono_ = +-mono
    ; _*-mono_ = *-mono
    ; isPoset = 01ω-isPoset
    ; isSemiring = 01ω-isSemiring
    }
  }
  where
  +ω : AnnihilRight _+01ω_ ω#
  +ω 0# = refl
  +ω 1# = refl
  +ω ω# = refl

  +-mono : Mono _≤01ω_ _+01ω_
  +-mono ≤01ω-refl ≤01ω-refl = ≤01ω-refl
  +-mono {x} {.x} {y} {y'} ≤01ω-refl ω-bot =
    subst (_≤01ω (x +01ω y')) (sym (+ω x)) ω-bot
  +-mono ω-bot yle = ω-bot

  *-mono : Mono _≤01ω_ _*01ω_
  *-mono ≤01ω-refl ≤01ω-refl = ≤01ω-refl
  *-mono {0#} {.0#} {.ω#} {y'} ≤01ω-refl ω-bot = ≤01ω-refl
  *-mono {1#} {.1#} {.ω#} {y'} ≤01ω-refl ω-bot = ω-bot
  *-mono {ω#} {.ω#} {.ω#} {y'} ≤01ω-refl ω-bot = ω-bot
  *-mono {.ω#} {x'} {.ω#} {y'} ω-bot ω-bot = ω-bot
  *-mono {.ω#} {x'} {0#} {.0#} ω-bot ≤01ω-refl =
    subst (0# ≤01ω_) (sym (snd annihil x')) ≤01ω-refl
    where open Semiring 01ωSemiring
  *-mono {.ω#} {x'} {1#} {.1#} ω-bot ≤01ω-refl = ω-bot
  *-mono {.ω#} {x'} {ω#} {.ω#} ω-bot ≤01ω-refl = ω-bot

module _ where
  open MeetSemilatticeSemiring hiding (_+-mono_; _*-mono_)

  01ωMeetSemilatticeSemiring : MeetSemilatticeSemiring lzero
  _≤_ 01ωMeetSemilatticeSemiring = _
  e0 01ωMeetSemilatticeSemiring = _
  e1 01ωMeetSemilatticeSemiring = _
  _+_ 01ωMeetSemilatticeSemiring = _
  _*_ 01ωMeetSemilatticeSemiring = _
  meet 01ωMeetSemilatticeSemiring = _
  isMeetSemilatticeSemiring 01ωMeetSemilatticeSemiring = record
    { _+-mono_ = _+-mono_
    ; _*-mono_ = _*-mono_
    ; isMeetSemilattice = 01ω-isMeetSemilattice
    ; isSemiring = 01ω-isSemiring
    }
    where open Posemiring 01ωPosemiring
  --01ωMeetSemilatticeSemiring = record
  --  { isMeetSemilatticeSemiring = record
  --    { _+-mono_ = _+-mono_
  --    ; _*-mono_ = _*-mono_
  --    ; isMeetSemilattice = 01ω-isMeetSemilattice
  --    ; isSemiring = 01ω-isSemiring
  --    }
  --  }
  --  where open Posemiring 01ωPosemiring

open MeetSemilatticeSemiring 01ωMeetSemilatticeSemiring

0#-top : forall {x} -> 0# ≤ x -> 0# == x
0#-top ≤01ω-refl = refl
1#-top : forall {x} -> 1# ≤ x -> 1# == x
1#-top ≤01ω-refl = refl

0#-sum : (forall {x} y -> x + y == 0# -> x == 0#)
       × (forall x {y} -> x + y == 0# -> y == 0#)
0#-sum = l , r
  where
  l : forall {x} y -> x + y == 0# -> x == 0#
  l {0#} y eq = refl
  l {1#} 0# ()
  l {1#} 1# ()
  l {1#} ω# ()
  l {ω#} 0# ()
  l {ω#} 1# ()
  l {ω#} ω# ()

  r : forall x {y} -> x + y == 0# -> y == 0#
  r 0# {y} eq = eq
  r 1# {0#} ()
  r 1# {1#} ()
  r 1# {ω#} ()
  r ω# {y} ()

1#-sum : forall x y -> x + y == 1# -> x == 1# × y == 0# ⊎ x == 0# × y == 1#
1#-sum 0# y eq = inr (refl , eq)
1#-sum 1# 0# eq = inl (refl , refl)
1#-sum 1# 1# ()
1#-sum 1# ω# ()
1#-sum ω# y ()

{-+}
open import Quantified 01ωSetoid 01ωMeetSemilatticeSemiring

infixr 30 _=>_
_=>_ : QTy -> QTy -> QTy
_=>_ = _-[ ω# ]o_

w-t : forall S T -> nil |- (S -o S -o T) -o S => T
w-t S T = lam (lam (app (app (var (there here)) (var here)) (var here)))

w-r : forall S T -> nil |-[ tt ] w-t S T
w-r S T = lam (lam (app {G0 = sg->rho tt :: sg->rho tt :: nil} (==Zip refl)
                        (app (==Zip refl)
                             (var (≤01ω-refl :: ≤01ω-refl :: nil))
                             (var (≤01ω-refl :: ≤01ω-refl :: nil)))
                        (var (ω-bot :: ≤01ω-refl :: nil))))

w-r0 : forall S T -> nil |-[ ff ] w-t S T
w-r0 S T = lam (lam (app {G0 = sg->rho ff :: sg->rho ff :: nil} (==Zip refl)
                         (app (==Zip refl)
                              (var (≤01ω-refl :: ≤01ω-refl :: nil))
                              (var (≤01ω-refl :: ≤01ω-refl :: nil)))
                         (var (≤01ω-refl :: ≤01ω-refl :: nil))))

{-+}
w-r' : forall sg S T -> nil |-[ sg ] w-t S T
w-r' sg S T = lam (lam (app {G0 = sg->rho sg :: sg->rho sg :: nil} {!!}
                            (app {!!}
                                 (var (≤01ω-refl :: ≤01ω-refl :: nil))
                                 (var (≤01ω-refl :: ≤01ω-refl :: nil)))
                            (var (ω-bot :: ≤01ω-refl :: nil))))
  --where
  --lemma1 : forall sg' -> 1# ω#
{+-}
{+-}
