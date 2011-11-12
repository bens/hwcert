module Adder where

open import Data.Nat            using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (module SemiringSolver)
open import Data.Product        using (∃₂; _×_; _,_)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Function            using (_$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym; module ≡-Reasoning)

open import Digital.OpSpec
  using (_b-nand_; _b-and_; rewriteAnd; _b-xor_; rewriteXor)

-- Exponentiation.
infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ 0 = 1
x ^ (suc e) = x * (x ^ e)

-- The indexed bit representation
data Bit : ℕ → Set where
  O      : Bit 0
  I      : Bit 1
  _nand_ : ∀ {m n} → Bit m → Bit n → Bit (m b-nand n)

_and_ : ∀ {m n} → Bit m → Bit n → Bit (m b-and n)
_and_ {m}{n} x y rewrite sym (rewriteAnd m n) =
  (x nand y) nand (x nand y)

_xor_ : ∀ {m n} → Bit m → Bit n → Bit (m b-xor n)
_xor_ {m}{n} x y rewrite sym (rewriteXor m n) =
  (x nand (x nand y)) nand (y nand (x nand y))

-- Proof that all bits have index 0 or 1
bounded : ∀ {n} → Bit n → n ≡ 0 ⊎ n ≡ 1
bounded O = inj₁ refl
bounded I = inj₂ refl
bounded (x nand y) with bounded x | bounded y
bounded (_nand_ {.0}{.0} x y) | inj₁ refl | inj₁ refl = inj₂ refl
bounded (_nand_ {.0}{.1} x y) | inj₁ refl | inj₂ refl = inj₂ refl
bounded (_nand_ {.1}{.0} x y) | inj₂ refl | inj₁ refl = inj₂ refl
bounded (_nand_ {.1}{.1} x y) | inj₂ refl | inj₂ refl = inj₁ refl

-- Collections of bits, indexed by their unsigned value.
-- The last bit added is the MSB.
infixr 5 _∷_
data Bits : ℕ → ℕ → Set where
  [] : Bits 0 0
  _∷_ : ∀ {w m n} (b : Bit m) (bs : Bits w n)
        → Bits (1 + w) (2 ^ w * m + n)

-- Split off the MSB of a Bits collection.
split1 : ∀ {w val}
       → (xs : Bits (1 + w) val)
       → ∃₂ λ m n → Bit m × Bits w n × (2 ^ w * m + n ≡ val)
split1 (b ∷ bs) with bounded b
split1 (b ∷ bs) | inj₁ refl = _ , _ , b , bs , refl
split1 (b ∷ bs) | inj₂ refl = _ , _ , b , bs , refl


-- Add two bits together.
module HalfAdder where
  spec = λ (m n : ℕ)
       → (m b-and n + (m b-and n + 0) + (m b-xor n + 0 + 0))

  impl : ∀ {m n} → Bit m → Bit n → Bits 2 (spec m n)
  impl x y = x and y ∷ x xor y ∷ []

  add : ∀ {m n} → Bit m → Bit n → Bits 2 (m + n)
  add {m}{n} x y = subst (Bits 2) (p x y) (impl x y)
    where
    p : ∀ {m n} → Bit m → Bit n → spec m n ≡ m + n
    p x y with bounded x | bounded y
    p x y | inj₁ refl | inj₁ refl = refl
    p x y | inj₁ refl | inj₂ refl = refl
    p x y | inj₂ refl | inj₁ refl = refl
    p x y | inj₂ refl | inj₂ refl = refl


-- Add three bits together.
module FullAdder where
  spec = λ (m n o : ℕ)
       → (2 * ((m b-xor n) b-nand o) b-nand (m b-nand n))
       + (1 * (m b-xor n) b-xor o + 0)

  impl : ∀ {m n o} → Bit m → Bit n → Bit o → Bits 2 (spec m n o)
  impl x y z = (x⊕y nand z) nand (x nand y) ∷ x⊕y xor z ∷ []
    where x⊕y = x xor y

  add : ∀ {m n o} → Bit m → Bit n → Bit o → Bits 2 (m + n + o)
  add {m}{n}{o} x y z = subst (Bits 2) (p x y z) (impl x y z)
    where
    p : ∀ {m n o} → Bit m → Bit n → Bit o → spec m n o ≡ m + n + o
    p x y z with bounded x | bounded y | bounded z
    ... | inj₁ refl | inj₁ refl | inj₁ refl = refl
    ... | inj₁ refl | inj₁ refl | inj₂ refl = refl
    ... | inj₁ refl | inj₂ refl | inj₁ refl = refl
    ... | inj₁ refl | inj₂ refl | inj₂ refl = refl
    ... | inj₂ refl | inj₁ refl | inj₁ refl = refl
    ... | inj₂ refl | inj₁ refl | inj₂ refl = refl
    ... | inj₂ refl | inj₂ refl | inj₁ refl = refl
    ... | inj₂ refl | inj₂ refl | inj₂ refl = refl


-- Add two n-bit numbers together.
module RippleAdder where
  module Lemma (w : ℕ) where
    open SemiringSolver using (solve; _:+_; _:*_; _:=_; con)
    2ʷ = 2 ^ w

    #1 : ∀ bc bx by n
         → 2ʷ * (bx + by + bc) + n
         ≡ 2ʷ * (bx + by) + (2ʷ * bc + n)
    #1 bc bx by n =
      solve 5 (λ 2ʷ' bc' bx' by' n'
               → 2ʷ' :* (bx' :+ by' :+ bc') :+ n'
              := 2ʷ' :* (bx' :+ by') :+ (2ʷ' :* bc' :+ n'))
            refl 2ʷ bc bx by n

    #2 : ∀ bc bx by bxs bys
         → 2ʷ * (bx + by) + (bxs + bys + bc)
         ≡ (2ʷ * bx + bxs) + (2ʷ * by + bys) + bc
    #2 bc bx by bxs bys =
      solve 6 (λ 2ʷ' bx' bxs' by' bys' bc'
               → 2ʷ' :* (bx' :+ by') :+ (bxs' :+ bys' :+ bc')
              := 2ʷ' :* bx' :+ bxs' :+ (2ʷ' :* by' :+ bys') :+ bc')
            refl 2ʷ bx bxs by bys bc

    #3 : ∀ bc bx n
         → (2 ^ (1 + w) * bc) + (2ʷ * bx + n)
         ≡ 2ʷ * (2 * bc + (1 * bx + 0)) + n
    #3 bx bc val =
      solve 4 (λ 2ʷ' bx' bc' val'
               → let 0' = con 0 in
                 (2ʷ' :+ (2ʷ' :+ 0')) :* bc' :+ (2ʷ' :* bx' :+ val')
              := 2ʷ' :* (bc' :+ (bc' :+ 0') :+ (bx' :+ 0' :+ 0')) :+ val')
            refl 2ʷ bc bx val


  add : {w m n : ℕ}
      → Bits w m → Bits w n
      → {c : ℕ} → Bit c
      → Bits (1 + w) (m + n + c)
  add {.0} [] [] c with bounded c
  add {.0} [] [] c | inj₁ refl = c ∷ []
  add {.0} [] [] c | inj₂ refl = c ∷ []
  add {suc w} (_∷_ {.w} x xs) (y ∷ ys) c with split1 (add xs ys c)
  add {suc w} (_∷_ {.w} {bx} {bxs} x xs) (_∷_ {.w} {by} {bys} y ys) {bc} c
    | bc′ , bsum , c′ , sum , prf
    = subst (Bits (2 + w)) main-proof $
        go (FullAdder.add x y c′) sum
    where
      2ʷ = 2 ^ w
      go : ∀ {bx n} → Bits 2 bx → Bits w n
         → Bits (2 + w) (2ʷ * bx + n)
      go {._}{n} (_∷_ {m = bc} c (_∷_ {m = bx} x [])) xs
        = subst (Bits (2 + w)) (Lemma.#3 w bc bx n) (c ∷ x ∷ xs)

      open ≡-Reasoning
      main-proof =
        begin
          2ʷ * (bx + by + bc′) + bsum
                                    ≡⟨ Lemma.#1 w bc′ bx by bsum ⟩
          2ʷ * (bx + by) + (2ʷ * bc′ + bsum)
                                    ≡⟨ cong (_+_ (2ʷ * (bx + by))) prf ⟩
          2ʷ * (bx + by) + (bxs + bys + bc)
                                    ≡⟨ Lemma.#2 w bc bx by bxs bys ⟩
          2ʷ * bx + bxs + (2ʷ * by + bys) + bc ∎
