open import Setoid as Setoid'
open import Structure

module DCC {c l} (C : Set c) (L : Lattice (==-Setoid C) l) where

open import Common

open import Bidirectional {l' = l} (List C) {!!}
