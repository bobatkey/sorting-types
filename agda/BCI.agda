open import Setoid as Setoid'

module BCI {a l} (S : Setoid a l) where

open import Common

open Setoid S renaming (C to A)

record IsBCI (_·_ : A -> A -> A) (B C I : A) : Set (a ⊔ l) where
  field
    Bxyz : forall x y z -> ((B · x) · y) · z ≈ x · (y · z)
    Cxyz : forall x y z -> ((C · x) · y) · z ≈ (x · z) · y
    Ix   : forall x     ->             I · x ≈ x

record BCI : Set (a ⊔ l) where
  infixl 8 _·_
  field
    _·_   : A -> A -> A
    B C I : A
    isBCI : IsBCI _·_ B C I
  open IsBCI isBCI public

record IsBCI! (_·_ : A -> A -> A) (B C I K W D δ F : A) (! : A -> A) : Set (a ⊔ l) where
  field
    Kx!y  : forall x y ->   (K · x) · ! y ≈ x
    Wx!y  : forall x y ->   (W · x) · ! y ≈ (x · y) · y
    D!x   : forall x   ->         D · ! x ≈ x
    δ!x   : forall x   ->         D · ! x ≈ ! (! x)
    F!x!y : forall x y -> (F · ! x) · ! y ≈ ! (x · y)
    isBCI : IsBCI _·_ B C I
  open IsBCI isBCI public

record BCI! : Set (a ⊔ l) where
  infixl 8 _·_
  field
    _·_   : A -> A -> A
    B C I K W D δ F : A
    ! : A -> A
    isBCI! : IsBCI! _·_ B C I K W D δ F !
  open IsBCI! isBCI! public

  bci : BCI
  bci = record { isBCI = isBCI }
