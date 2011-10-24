{-# OPTIONS --universe-polymorphism #-}

open import Data.Nat using (ℕ)
module Digital.Bits {ℓ} (Bit : ℕ → Set ℓ) where

open import Data.Nat using (suc; _+_; _*_)
open import Digital.NatExtra as ℕ-E using (_^_)

infixr 5 _∷_
data Bits : ℕ → ℕ → Set ℓ where
  [] : Bits 0 0
  _∷_ : ∀ {w m n} (b : Bit m) (bs : Bits w n)
        → Bits (suc w) (2 ^ w * m + n)
