module Semantics.Calc where

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import OpSpec
open import Signal

module CalcSignals where
  data CBit : ℕ → Set where
    CO : CBit 0
    CI : CBit 1

  private
    cnand : ∀ {m n} → CBit m → CBit n → CBit (m b-nand n)
    cnand CO CO = CI
    cnand CO CI = CI
    cnand CI CO = CI
    cnand CI CI = CO

    cbind : ∀ {x} {a : Set} → CBit x → (CBit x → a) → a
    cbind x f = f x

    cbounded : ∀ {n} → CBit n → n ≡ 0 ⊎ n ≡ 1
    cbounded CO = inj₁ refl
    cbounded CI = inj₂ refl

  signals : Signals CBit
  signals = record
    { _nand_  = cnand
    ; bind    = cbind
    ; O       = CO
    ; I       = CI
    ; bounded = cbounded
    }

eval : (∀ S → (s : Signals S) → ∃ S) → ℕ
eval f = proj₁ (f _ CalcSignals.signals)
