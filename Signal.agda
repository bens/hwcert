module Signal where

open import Data.Nat
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

open import OpSpec

record Signals (S : ℕ → Set) : Set₁ where
  field
    _nand_  : ∀ {x y} → S x → S y → S (x b-nand y)
    bind    : ∀ {x} {a : Set} → S x → (S x → a) → a
    O       : S 0
    I       : S 1
    bounded : ∀ {n} → S n → n ≡ 0 ⊎ n ≡ 1

record SigOps {S} (signals : Signals S) : Set₁ where
  open Signals signals
  field
    not   : ∀ {x}   → S x → S (b-not x)
    _and_ : ∀ {x y} → S x → S y → S (x b-and y)
    _or_  : ∀ {x y} → S x → S y → S (x b-or y)
    _xor_ : ∀ {x y} → S x → S y → S (x b-xor y)
  open Signals signals public

defaultSigOps : ∀ {S} (s : Signals S) → SigOps s
defaultSigOps {S} ss = record
  { not   = λ   {n} x   → subst S (rewriteNot n)   (implNot x)
  ; _and_ = λ {m n} x y → subst S (rewriteAnd m n) (implAnd x y)
  ; _or_  = λ {m n} x y → subst S (rewriteOr  m n) (implOr  x y)
  ; _xor_ = λ {m n} x y → subst S (rewriteXor m n) (implXor x y)
  }
  where
    open Signals ss using (_nand_; bind)
    implNot : ∀ {n} → S n → S (defNot n)
    implNot x = bind x $ λ x′ → x′ nand x′

    implAnd : ∀ {m n} → S m → S n → S (defAnd m n)
    implAnd x y = bind (x nand y) implNot

    implOr : ∀ {m n} → S m → S n → S (defOr m n)
    implOr x y = (implNot x) nand (implNot y)

    implXor : ∀ {m n} → S m → S n → S (defXor m n)
    implXor x y  = bind (x nand y) $ λ xy → (x nand xy) nand (y nand xy)

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

open import Data.String

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
