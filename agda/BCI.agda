open import Setoid as Setoid'

module BCI {a l} (S : Setoid a l) where

open import Common hiding (refl)

open Setoid S renaming (C to A)

record IsBCI (_·_ : A -> A -> A) (B C I : A) : Set (a ⊔ l) where
  infixl 8 _·-cong_
  field
    Bxyz : forall x y z -> ((B · x) · y) · z ≈ x · (y · z)
    Cxyz : forall x y z -> ((C · x) · y) · z ≈ (x · z) · y
    Ix   : forall x     ->             I · x ≈ x
    _·-cong_ : forall {x x' y y'} -> x ≈ x' -> y ≈ y' -> x · y ≈ x' · y'

record BCI : Set (a ⊔ l) where
  infixl 8 _·_
  field
    _·_   : A -> A -> A
    B C I : A
    isBCI : IsBCI _·_ B C I
  open IsBCI isBCI public

record IsBCI! (_·_ : A -> A -> A) (B C I K W D δ F : A) (! : A -> A)
              : Set (a ⊔ l) where
  field
    Kx!y  : forall x y ->   (K · x) · ! y ≈ x
    Wx!y  : forall x y ->   (W · x) · ! y ≈ (x · y) · y
    D!x   : forall x   ->         D · ! x ≈ x
    δ!x   : forall x   ->         δ · ! x ≈ ! (! x)
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

module BCI-Combinators (Alg : BCI) where
  open BCI Alg

  infixr 5 _,C_
  _,C_ : A -> A -> A
  a ,C b = C · (C · I · a) · b

  appC : A
  appC = C · I · I

  appC-comp : forall a b -> appC · (a ,C b) ≈ a · b
  appC-comp a b =
    appC · (a ,C b)                    ≈[ refl ]≈
    C · I · I · (C · (C · I · a) · b)  ≈[ Cxyz _ _ _ ]≈
    I · (C · (C · I · a) · b) · I      ≈[ Ix _ ·-cong refl ]≈
    C · (C · I · a) · b · I            ≈[ Cxyz _ _ _ ]≈
    C · I · a · I · b                  ≈[ Cxyz _ _ _ ·-cong refl ]≈
    I · I · a · b                      ≈[ Ix _ ·-cong refl ·-cong refl ]≈
    I · a · b                          ≈[ Ix _ ·-cong refl ]≈
    a · b                              QED
    where open SetoidReasoning S
