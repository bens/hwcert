{-# OPTIONS --universe-polymorphism #-}

module Digital.Signals where

open import Level
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality

open import Digital.OpSpec

record Signals {ℓ} (S : ℕ → Set ℓ) : Set (suc ℓ) where
  field
    _nand_  : ∀ {x y} → S x → S y → S (x b-nand y)
    bind    : ∀ {x} {a : Set ℓ} → S x → (S x → a) → a
    O       : S 0
    I       : S 1
    bounded : ∀ {n} → S n → n ≡ 0 ⊎ n ≡ 1

record SigOps {ℓ} {S : ℕ → Set ℓ} (signals : Signals S) : Set (suc ℓ) where
  open Signals signals
  field
    not   : ∀ {x}   → S x → S (b-not x)
    _and_ : ∀ {x y} → S x → S y → S (x b-and y)
    _or_  : ∀ {x y} → S x → S y → S (x b-or y)
    _xor_ : ∀ {x y} → S x → S y → S (x b-xor y)
  open Signals signals public

defaultSigOps : ∀ {ℓ} {S : ℕ → Set ℓ} (s : Signals S) → SigOps s
defaultSigOps {_} {S} ss = record
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
