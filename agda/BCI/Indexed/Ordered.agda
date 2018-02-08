open import Setoid as Setoid'
open import Structure

module BCI.Indexed.Ordered
  {a b l m m'} (S : Setoid a l) (R : Setoid b m) (Rs : Posemiring R m')
  where

open import Common using (_⊔_)
open import BCI S
open import BCI.Indexed S R (Posemiring.semiring Rs)

open Setoid S renaming (C to A)
private
  module R = Setoid R
open Posemiring Rs

record IsBCIρ≤ (_·_ : A -> A -> A) (B C I K D : A) (W δ : (π ρ : R.C) -> A)
               (F : R.C -> A) (! : R.C -> A -> A)
               (u : {π ρ : R.C} -> ρ ≤ π -> A) : Set (a ⊔ l ⊔ b ⊔ m') where
  field
    u!x : forall {π ρ} (le : π ≤ ρ) (x : A) -> u le · (! π x) ≈ ! ρ x
    isBCIρ : IsBCIρ _·_ B C I K D W δ F !
  open IsBCIρ isBCIρ public

record BCIρ≤ : Set (a ⊔ l ⊔ b ⊔ m') where
  infixl 8 _·_
  field
    _·_   : A -> A -> A
    B C I K D : A
    W δ : (π ρ : R.C) -> A
    F : R.C -> A
    ! : R.C -> A -> A
    u : {π ρ : R.C} -> π ≤ ρ -> A
    isBCIρ≤ : IsBCIρ≤ _·_ B C I K D W δ F ! u
  open IsBCIρ≤ isBCIρ≤ public

  bciρ : BCIρ
  bciρ = record { isBCIρ = isBCIρ }
  open BCIρ bciρ public using (bci)

