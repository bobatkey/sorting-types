open import Setoid as Setoid'

module BCI {a l} (S : Setoid a l) where

open import Common hiding (refl; sym)

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

  open SetoidReasoning S

  infixr 5 _,C_ _,C-cong_
  _,C_ : A -> A -> A
  a ,C b = C · (C · I · a) · b

  ,C-comp : forall a b f -> (a ,C b) · f ≈ f · a · b
  ,C-comp a b f =
    (a ,C b) · f             ≈[ refl ]≈
    C · (C · I · a) · b · f  ≈[ Cxyz _ _ _ ]≈
    C · I · a · f · b        ≈[ Cxyz _ _ _ ·-cong refl ]≈
    I · f · a · b            ≈[ Ix _ ·-cong refl ·-cong refl ]≈
    f · a · b                QED

  _,C-cong_ : forall {a a' b b'} -> a ≈ a' -> b ≈ b' -> a ,C b ≈ a' ,C b'
  aq ,C-cong bq = refl ·-cong (refl ·-cong aq) ·-cong bq

  pairC : A
  pairC = B · C · (C · I)

  pairC-comp : forall a b -> pairC · a · b ≈ a ,C b
  pairC-comp a b = Bxyz _ _ _ ·-cong refl

  pmC : A
  pmC = C · I

  pmC-comp : forall f a b -> pmC · f · (a ,C b) ≈ f · a · b
  pmC-comp f a b =
    pmC · f · (a ,C b)    ≈[ refl ]≈
    C · I · f · (a ,C b)  ≈[ Cxyz _ _ _ ]≈
    I · (a ,C b) · f      ≈[ Ix _ ·-cong refl ]≈
    (a ,C b) · f          ≈[ ,C-comp _ _ _ ]≈
    f · a · b             QED

  appC : A
  appC = pmC · I

  appC-comp : forall a b -> appC · (a ,C b) ≈ a · b
  appC-comp a b =
    appC · (a ,C b)                    ≈[ refl ]≈
    pmC · I · (a ,C b)                 ≈[ pmC-comp _ _ _ ]≈
    I · a · b                          ≈[ Ix _ ·-cong refl ]≈
    a · b                              QED

  app-flipC : A
  app-flipC = pmC · (C · I)

  app-flipC-comp : forall a b -> app-flipC · (a ,C b) ≈ b · a
  app-flipC-comp a b =
    app-flipC · (a ,C b)           ≈[ refl ]≈
    pmC · (C · I) · (a ,C b)       ≈[ pmC-comp _ _ _ ]≈
    (C · I) · a · b                ≈[ Cxyz _ _ _ ]≈
    I · b · a                      ≈[ Ix _ ·-cong refl ]≈
    b · a                          QED
