module Digital.Bit where

open import Algebra
open import Data.Nat as N
import Data.Nat.Properties as N
open import Data.Nat.Properties using (_+-mono_)
open N.SemiringSolver using (solve; _:+_; _:*_; _:=_; con)
open import Data.Product as P
open import Data.Sum as S
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- local
open import Digital.NatExtra as ℕ-E using (_^_)

private
  module CS = CommutativeSemiring N.commutativeSemiring
  module DTO = DecTotalOrder N.decTotalOrder

module Bit where
  data Bit : ℕ → Set where
    O : Bit 0
    I : Bit 1

  bounded : ∀ {n} → Bit n → n ≤ 1
  bounded O = z≤n
  bounded I = s≤s z≤n

  unique : ∀ {n} → (x y : Bit n) → x ≡ y
  unique O O = refl
  unique I I = refl

open Bit public using (Bit; O; I)

module Bits where
  infixr 5 _∷_
  data Bits : ℕ → ℕ → Set where
    [] : Bits 0 0
    _∷_ : ∀ {w m n}
        → (b : Bit m) → (bs : Bits w n)
        → Bits (suc w) (2 ^ w * m + n)

  private
    -- some test numbers
    b₁ = O ∷ O ∷ O ∷ I ∷ [] ∶ Bits 4 1
    b₂ = O ∷ O ∷ I ∷ O ∷ [] ∶ Bits 4 2
    b₃ = O ∷ O ∷ I ∷ I ∷ [] ∶ Bits 4 3
    b₄ = O ∷ I ∷ O ∷ O ∷ [] ∶ Bits 4 4
    b₅ = O ∷ I ∷ O ∷ I ∷ [] ∶ Bits 4 5
    b₆ = O ∷ I ∷ I ∷ O ∷ [] ∶ Bits 4 6
    b₇ = O ∷ I ∷ I ∷ I ∷ [] ∶ Bits 4 7
    b₈ = I ∷ O ∷ O ∷ O ∷ [] ∶ Bits 4 8

  open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)

  bounded : ∀ {w n} → Bits w n → n < 2 ^ w
  bounded [] = s≤s z≤n
  bounded (b ∷ bs) = go b bs
    where
    go : ∀ {w m n} → Bit m → Bits w n → 2 ^ w * m + n < 2 ^ (1 + w)
    go {w}{m}{n} b bs = let 2ʷ = 2 ^ w in
      start suc (2ʷ * m) + n
        ≡⟨ cong suc (CS.+-comm (2ʷ * m) n) ⟩'
            suc n + (2ʷ * m)
        ≡⟨ cong (_+_ (suc n)) (CS.*-comm 2ʷ m) ⟩'
            suc n + (m * 2ʷ)
        ≤⟨ bounded bs +-mono ℕ-E.m≤1→m*n≤n (Bit.bounded b) 2ʷ ⟩
            2ʷ + 2ʷ
        ≡⟨ cong (_+_ 2ʷ) (CS.+-comm 0 2ʷ) ⟩'
            2ʷ + (2ʷ + 0) □

  b0 : ∀ {w} → Bits w 0
  b0 {zero} = []
  b0 {suc w} = subst (Bits (suc w)) p (O ∷ b0 {w})
    where p = cong (flip _+_ 0) $ CS.*-comm (2 ^ w) 0

  incr : ∀ {w n} → Bits w n
       → Bits w (suc n) ⊎ (Bits (suc w) (suc n) × suc n ≡ 2 ^ w)
  incr [] = inj₂ (I ∷ [] , refl)
  incr (_∷_ {w}{m}{n} b bs) with incr bs
  ... | inj₁ bs′ rewrite sym (ℕ-E.swapSuc (2 ^ w * m) n) = inj₁ (b ∷ bs′)
  incr (_∷_ {_}{._}{n} O bs) | inj₂ (bs′ , prf) rewrite sym prf | CS.*-comm n 0
    = inj₁ bs′
  incr (_∷_ {w}{.1}{n} I bs) | inj₂ (bs′ , prf) rewrite sym prf
    = inj₂ (subst (Bits (2 + w)) lemma (I ∷ b0) ,
              solve 1 (λ n' → con 1 :+ (con 1 :+ (n' :* con 1 :+ n'))
                           := con 1 :+ (n' :+ (con 1 :+ (n' :+ con 0))))
                    refl n)
    where
    lemma : (2 ^ w + (2 ^ w + 0)) * 1 + 0 ≡ 2 + (n * 1 + n)
    lemma rewrite sym prf
        | CS.*-comm n 1 | CS.+-comm n 0
        | CS.*-comm (n + suc n) 1
        | CS.+-comm (n + suc n) 0
        | CS.+-comm (n + suc n) 0
      = solve 1 (λ n' → con 1 :+ (n' :+ (con 1 :+ n'))
                     := con 1 :+ (con 1 :+ (n' :+ n')))
              refl n

  repr : ∀ n → Σ[ w ∶ ℕ ] Bits w n
  repr n = go n (DTO.reflexive refl) (subst (Bits 0) (ℕ-E.0≡n∸n n) [])
    where
    go : ∀ {w} m → m ≤ n → Bits w (n ∸ m) → Σ[ w′ ∶ ℕ ] Bits w′ n
    go zero  z≤n bs = , bs
    go (suc m) m<n bs with incr bs
    ... | inj₁ bs′
      = go m (ℕ-E.≤-step′ m<n) $ subst (Bits _) (ℕ-E.sn∸sm≡n∸m m<n) bs′
    ... | inj₂ (bs′ , _)
      = go m (ℕ-E.≤-step′ m<n) $ subst (Bits _) (ℕ-E.sn∸sm≡n∸m m<n) bs′

  split1 : ∀ {w val}
         → (xs : Bits (suc w) val)
         → ∃₂ λ m n → Bit m × Bits w n × (2 ^ w * m + n ≡ val)
  split1 {w}{.(2 ^ w * 0 + n)} (_∷_ {.w}{.0}{n} O bs)
    = 0 , n , O , bs , refl
  split1 {w}{.(2 ^ w * 1 + n)} (_∷_ {.w}{.1}{n} I bs)
    = 1 , n , I , bs , refl

open Bits public using (Bits; []; _∷_)
