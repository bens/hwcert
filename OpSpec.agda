module OpSpec where

open import Data.Nat using (ℕ; suc; zero; _≤_; s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- NAND
_b-nand_ : ℕ → ℕ → ℕ
_b-nand_      0       0  = 1
_b-nand_      0  (suc _) = 1
_b-nand_ (suc _)      0  = 1
_b-nand_ (suc _) (suc _) = 0

nand-bounded : ∀ {m n} → m ≤ 1 → n ≤ 1 → m b-nand n ≤ 1
nand-bounded  z≤n     z≤n    = s≤s z≤n
nand-bounded  z≤n    (s≤s _) = s≤s z≤n
nand-bounded (s≤s _)  z≤n    = s≤s z≤n
nand-bounded (s≤s _) (s≤s _) = z≤n

-- NOT
defNot = λ (n : ℕ) → n b-nand n

b-not : ℕ → ℕ
b-not      0  = 1
b-not (suc _) = 0

rewriteNot : ∀ n → defNot n ≡ b-not n
rewriteNot      0  = refl
rewriteNot (suc _) = refl

-- AND
defAnd = λ (m n : ℕ) → (m b-nand n) b-nand (m b-nand n)

_b-and_ : ℕ → ℕ → ℕ
_b-and_      0       0  = 0
_b-and_      0  (suc _) = 0
_b-and_ (suc _)      0  = 0
_b-and_ (suc _) (suc _) = 1

rewriteAnd : ∀ m n → defAnd m n ≡ m b-and n
rewriteAnd      0       0  = refl
rewriteAnd      0  (suc _) = refl
rewriteAnd (suc _)      0  = refl
rewriteAnd (suc _) (suc _) = refl

-- OR
defOr = λ (m n : ℕ) → (m b-nand m) b-nand (n b-nand n)

_b-or_ : ℕ → ℕ → ℕ
_b-or_      0       0  = 0
_b-or_      0  (suc _) = 1
_b-or_ (suc _)      0  = 1
_b-or_ (suc _) (suc _) = 1

rewriteOr : ∀ m n → defOr m n ≡ m b-or n
rewriteOr      0       0  = refl
rewriteOr      0  (suc _) = refl
rewriteOr (suc _)      0  = refl
rewriteOr (suc _) (suc _) = refl

-- XOR
defXor = λ (m n : ℕ) →
           (m b-nand (m b-nand n)) b-nand (n b-nand (m b-nand n))

_b-xor_ : ℕ → ℕ → ℕ
_b-xor_      0       0  = 0
_b-xor_      0  (suc _) = 1
_b-xor_ (suc _)      0  = 1
_b-xor_ (suc _) (suc _) = 0

rewriteXor : ∀ m n → defXor m n ≡ m b-xor n
rewriteXor      0       0  = refl
rewriteXor      0  (suc _) = refl
rewriteXor (suc _)      0  = refl
rewriteXor (suc _) (suc _) = refl
