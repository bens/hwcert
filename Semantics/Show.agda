module Semantics.Show where

open import Data.Nat
open import Data.Product
open import Data.String
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

open import OpSpec
open import Signal

module ShowSignals where
  data Var : ℕ → Set where
    var′ : ∀ {n} → (n≤1 : n ≤ 1) → String → Var n

  private
    snand : ∀ {m n} → Var m → Var n → Var (m b-nand n)
    snand {m}{n} (var′ px x) (var′ py y) =
      var′ (nand-bounded px py) $ "(" ++ x ++ " nand " ++ y ++ ")"

    sbind : ∀ {x} {a : Set} → Var x → (Var x → a) → a
    sbind x f = f x

    sbounded : ∀ {n} → Var n → n ≡ 0 ⊎ n ≡ 1
    sbounded (var′      z≤n  _) = inj₁ refl
    sbounded (var′ (s≤s z≤n) _) = inj₂ refl

  signals : Signals Var
  signals = record
    { _nand_  = snand
    ; bind    = sbind
    ; O       = var′ z≤n "O"
    ; I       = var′ (s≤s z≤n) "I"
    ; bounded = sbounded
    }

  show : ∀ {n} → Var n → String
  show (var′ _ xs) = xs

show : (∀ {S} → (s : Signals S) → ∃ S) → String
show f = ShowSignals.show (proj₂ (f ShowSignals.signals))

private
  ex₀ : show (λ s → , Signals.O s) ≡ "O"
  ex₀ = refl

  ex₁ : show (λ s → , Signals._nand_ s (Signals.O s) (Signals.O s))
                    ≡ "(O nand O)"
  ex₁ = refl

  ex₂ : show (λ s → , Signals.bind s (Signals.O s)
                        (λ o → Signals._nand_ s o o))
                    ≡ "(O nand O)"
  ex₂ = refl
