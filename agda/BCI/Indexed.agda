open import Setoid as Setoid'
open import Structure

module BCI.Indexed {a b l m} (S : Setoid a l)
                   (R : Setoid b m) (semiring : Semiring R) where

open import Common using (_⊔_)
open import BCI S

open Setoid S renaming (C to A)
private
  module R = Setoid R
open Semiring semiring

record IsBCIρ (_·_ : A -> A -> A) (B C I K D : A) (W δ : (π ρ : R.C) -> A)
                (F : R.C -> A) (! : R.C -> A -> A) : Set (a ⊔ l ⊔ b) where
  field
    Kx!y  : forall x y     ->          (K · x) · ! e0 y ≈ x
    Wx!y  : forall π ρ x y -> (W π ρ · x) · ! (π + ρ) y ≈ (x · ! π y) · ! ρ y
    D!x   : forall x       ->                D · ! e1 x ≈ x
    δ!x   : forall π ρ x   ->       δ π ρ · ! (π * ρ) x ≈ ! π (! ρ x)
    F!x!y : forall ρ x y   ->     (F ρ · ! ρ x) · ! ρ y ≈ ! ρ (x · y)
    isBCI : IsBCI _·_ B C I
  open IsBCI isBCI public

record BCIρ : Set (a ⊔ l ⊔ b) where
  infixl 8 _·_
  field
    _·_   : A -> A -> A
    B C I K D : A
    W δ : (π ρ : R.C) -> A
    F : R.C -> A
    ! : R.C -> A -> A
    isBCIρ : IsBCIρ _·_ B C I K D W δ F !
  open IsBCIρ isBCIρ public

  bci : BCI
  bci = record { isBCI = isBCI }
