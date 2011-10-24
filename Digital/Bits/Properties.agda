{-# OPTIONS --universe-polymorphism #-}

open import Data.Nat using (ℕ)
open import Digital.Signals using (Signals)

module Digital.Bits.Properties
  (Bit : ℕ → Set)
  (signals : Signals Bit) where

open import Algebra using (module CommutativeSemiring)
open import Data.Nat using ( zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s
                           ; module ≤-Reasoning
                           ; _∸_ )
open import Data.Nat.Properties using (commutativeSemiring; _+-mono_)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
import Digital.Bits
open Digital.Bits Bit
open import Digital.NatExtra as ℕ-E using (_^_)
open import Function using (_$_; flip)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; subst₂)
open ≤-Reasoning
private
  module S = Digital.Signals.Signals signals
  module ℕ-CSR = CommutativeSemiring commutativeSemiring

-- Pad a Bits object with zeros, not changing its value
pad : ∀ {w d n} → Bits w n → Bits (w + d) n
pad {w} {zero} bs = subst₂ Bits (sym (proj₂ ℕ-CSR.+-identity w)) refl bs
pad {w} {suc d} {n} bs =
  subst₂ Bits (sym (ℕ-E.swapSuc w d)) p (S.O ∷ pad {d = d} bs)
  where p = cong (flip _+_ n) (ℕ-CSR.*-comm (2 ^ (w + d)) 0)

zeros : ∀ {w} → Bits w 0
zeros = pad []

bounded : ∀ {w n} → Bits w n → n < 2 ^ w
bounded [] = s≤s z≤n
bounded (_∷_ {w}{m}{n} b bs) = let 2ʷ = 2 ^ w in
  begin suc (2ʷ * m + n)
    ≡⟨ cong suc $ ℕ-CSR.+-comm (2ʷ * m) n ⟩
        suc n + (2ʷ * m)
    ≡⟨ cong suc $ cong (_+_ n) (ℕ-CSR.*-comm 2ʷ m) ⟩
        suc n + (m * 2ʷ)
    ≤⟨ bounded bs +-mono ℕ-E.m≤1→m*n≤n (bitBounded b) 2ʷ ⟩
        2ʷ + 2ʷ
    ≡⟨ cong (_+_ 2ʷ) $ sym (proj₂ ℕ-CSR.+-identity 2ʷ) ⟩
        2 * 2ʷ ∎
  where
  bitBounded : ∀ {n} → Bit n → n ≤ 1
  bitBounded b with S.bounded b
  ... | inj₁ refl = z≤n
  ... | inj₂ refl = s≤s z≤n

-- Split out the most significant bit with a certificate
split1 : ∀ {w val}
       → (xs : Bits (suc w) val)
       → ∃₂ λ m n → Bit m × Bits w n × (2 ^ w * m + n ≡ val)
split1 (b ∷ bs) with S.bounded b
split1 (b ∷ bs) | inj₁ refl = _ , _ , b , bs , refl
split1 (b ∷ bs) | inj₂ refl = _ , _ , b , bs , refl
