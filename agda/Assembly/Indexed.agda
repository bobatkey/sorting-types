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

bangA-0 : forall {c e r} (B : Assembly c e r) -> bangA e0 B =A> oneA
bangA-0 B = record
  { f = constE $E <>
  ; af = K · I
  ; realises = \ { {u} {au} (av , aq , r) ->
                 K · I · au       ≈[ refl ·-cong aq ]≈
                 K · I · ! e0 av  ≈[ Kx!y I av ]≈
                 I                QED
                 }
  }
  where
  open SetoidReasoning S

bangA-1 : forall {c e r} (B : Assembly c e r) -> bangA e1 B =A> B
bangA-1 B = record
  { f = idE B.U
  ; af = D
  ; realises = \ { {u} {au} (av , aq , r) ->
                 B.|=-resp (sym (D · au       ≈[ refl ·-cong aq ]≈
                                 D · ! e1 av  ≈[ D!x av ]≈
                                 av           QED))
                           B.refl
                           r
                 }
  }
  where
  module B = Assembly B
  open SetoidReasoning S
