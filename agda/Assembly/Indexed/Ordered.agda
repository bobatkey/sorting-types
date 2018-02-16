open import Setoid as Setoid'
open import BCI.Indexed
open import BCI.Indexed.Ordered
open import Structure

module Assembly.Indexed.Ordered
  {a l b m m'} {S : Setoid a l} {R : Setoid b m}
  {Rs : Posemiring R m'} (Alg : BCIρ≤ S R Rs) where

open import Common renaming (_*_ to _×_) hiding (refl; sym; trans)

open Setoid S renaming (C to A)
private
  module R = Setoid R
open Posemiring Rs
open BCIρ≤ Alg

open import Assembly bci
open import Assembly.Indexed bciρ

bangA-≤ : forall {c e r π ρ} (le : π ≤ ρ) (B : Assembly c e r) ->
          bangA π B =A> bangA ρ B
bangA-≤ {π = π} {ρ} le B =
  idE _ , u le , \ { {_} {au} (av , auq , r) ->
                   av
                   , u le · au      ≈[ refl ·-cong auq ]≈
                     u le · ! π av  ≈[ u!x le av ]≈
                     ! ρ av         QED
                   , r
                   }
  where
  module B = Assembly B
  open SetoidReasoning S
