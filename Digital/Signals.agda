module Digital.Signals where

open import Level
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Vec using (Vec; _∷_; []; take; drop)
open import Function
open import Relation.Binary.PropositionalEquality

import Digital.Bits
open import Digital.OpSpec
open import Digital.Signature

record Signals (S : ℕ → Set) : Set1 where
  open Digital.Bits S
  field
    _nand_  : ∀ {x y} → S x → S y → S (x b-nand y)
    bind    : ∀ {ni no}
              → (ti : Ty ni) (ii : IX⟦ ti ⟧)
              → (to : Ty no) (io : IX⟦ to ⟧)
              → T⟦ S ∣ ti ∶ ii ⟧ → S⟦ S ∣ ti ∶ ii ↦ to ∶ io ⟧
              → T⟦ S ∣ to ∶ io ⟧
    O       : S 0
    I       : S 1
    bounded : ∀ {n} → S n → n ≡ 0 ⊎ n ≡ 1

module Utilities {S : ℕ → Set} (signals : Signals S) where
  open Signals signals using (bind)
  open Digital.Bits S

  bind1-1 : ∀ {m n} → S m → (S m → S n) → S n
  bind1-1 = bind bit _ bit _

  bind1-n : ∀ {w m n} → S m → (S m → Bits w n) → Bits w n
  bind1-n {w} = bind bit _ (bits w) _

  bind2-1 : ∀ {m n o} → S m → S n → (S m → S n → S o) → S o
  bind2-1 x y = bind (bit t+ bit) _ bit _ (x , y) ∘ uncurry

record SigOps {S : ℕ → Set} (signals : Signals S) : Set1 where
  open Signals signals
  field
    not   : ∀ {x}   → S x → S (b-not x)
    _and_ : ∀ {x y} → S x → S y → S (x b-and y)
    _or_  : ∀ {x y} → S x → S y → S (x b-or y)
    _xor_ : ∀ {x y} → S x → S y → S (x b-xor y)
  open Signals signals public

defaultSigOps : ∀ {S : ℕ → Set} (s : Signals S) → SigOps s
defaultSigOps {S} signals = record
  { not   = λ   {n} x   → subst S (rewriteNot n)   (implNot x)
  ; _and_ = λ {m n} x y → subst S (rewriteAnd m n) (implAnd x y)
  ; _or_  = λ {m n} x y → subst S (rewriteOr  m n) (implOr  x y)
  ; _xor_ = λ {m n} x y → subst S (rewriteXor m n) (implXor x y)
  }
  where
    open Signals signals using (_nand_; bind)
    open Utilities signals

    implNot : ∀ {n} → S n → S (defNot n)
    implNot x = bind1-1 x $ λ x′ → x′ nand x′

    implAnd : ∀ {m n} → S m → S n → S (defAnd m n)
    implAnd x y = bind1-1 (x nand y) $ implNot

    implOr : ∀ {m n} → S m → S n → S (defOr m n)
    implOr x y = (implNot x) nand (implNot y)

    implXor : ∀ {m n} → S m → S n → S (defXor m n)
    implXor x y = bind1-1 (x nand y) $ λ xy → (x nand xy) nand (y nand xy)
