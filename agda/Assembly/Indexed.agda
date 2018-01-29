open import Setoid as Setoid'
open import BCI.Indexed
open import Structure

module Assembly.Indexed {a l b m} {S : Setoid a l} {R : Setoid b m}
                        {Rs : Semiring R} (Alg : BCIρ S R Rs) where

open import Common renaming (_*_ to _×_) hiding (refl; sym; trans)

open Setoid S renaming (C to A)
private
  module R = Setoid R
open Semiring Rs
open BCIρ Alg

open import Assembly bci

bangA : forall {c e r} -> R.C -> Assembly c e r -> Assembly _ _ _
bangA ρ B = record
  { U = U
  ; _|=_ = \ a u -> Sg _ \ b -> a ≈ ! ρ b × b |= u
  ; realised = \ u -> let a , r = realised u in ! ρ a , a , refl , r
  ; |=-resp = \ { aq uq (b , split , r) ->
                  b , trans (sym aq) split , |=-resp refl uq r }
  }
  where
  open Assembly B hiding (_≈_; refl; sym; trans)
