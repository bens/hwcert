--
-- Largely taken from
--
--   Constructing Correct Circuits: Verification of Functional Aspects
--            of Hardware Specifications with Dependent Types
--
--             Edwin Brady, Kevin Hammond and James McKinna
--
-- http://www.cs.ru.nl/~james/RESEARCH/tfp2007.pdf
--




-- Boilerplate
module Adder where

open import Data.Nat            using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (module SemiringSolver)
open import Data.Product        using (∃₂; _×_; _,_)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Function            using (_$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym; module ≡-Reasoning)






--
-- Specifications of operations
--

module Specs where
  _nand-spec_ : ℕ → ℕ → ℕ
  _nand-spec_      0       0  = 1
  _nand-spec_      0  (suc _) = 1
  _nand-spec_ (suc _)      0  = 1
  _nand-spec_ (suc _) (suc _) = 0


  defAnd = λ (m n : ℕ) →
           (m nand-spec n) nand-spec (m nand-spec n)

  _and-spec_ : ℕ → ℕ → ℕ
  _and-spec_      0       0  = 0
  _and-spec_      0  (suc _) = 0
  _and-spec_ (suc _)      0  = 0
  _and-spec_ (suc _) (suc _) = 1

  rewriteAnd : ∀ m n → defAnd m n ≡ m and-spec n
  rewriteAnd      0       0  = refl
  rewriteAnd      0  (suc _) = refl
  rewriteAnd (suc _)      0  = refl
  rewriteAnd (suc _) (suc _) = refl


  defXor = λ (m n : ℕ) →
             (m nand-spec (m nand-spec n)) nand-spec
             (n nand-spec (m nand-spec n))

  _xor-spec_ : ℕ → ℕ → ℕ
  _xor-spec_      0       0  = 0
  _xor-spec_      0  (suc _) = 1
  _xor-spec_ (suc _)      0  = 1
  _xor-spec_ (suc _) (suc _) = 0

  rewriteXor : ∀ m n → defXor m n ≡ m xor-spec n
  rewriteXor      0       0  = refl
  rewriteXor      0  (suc _) = refl
  rewriteXor (suc _)      0  = refl
  rewriteXor (suc _) (suc _) = refl











open Specs

-- The indexed bit representation
data Bit : ℕ → Set where
  O      : Bit 0
  I      : Bit 1
  _nand_ : ∀ {m n} → Bit m → Bit n → Bit (m nand-spec n)

example₀ : Bit 0
example₀ = I nand I

_and_ : ∀ {m n} → Bit m → Bit n → Bit (m b-and n)
_and_ {m}{n} x y rewrite sym (rewriteAnd m n) =
  (x nand y) nand (x nand y)

_xor_ : ∀ {m n} → Bit m → Bit n → Bit (m b-xor n)
_xor_ {m}{n} x y rewrite sym (rewriteXor m n) =
  (x nand (x nand y)) nand (y nand (x nand y))

-- Proof that all bits have index 0 or 1
bounded : {n : ℕ} → Bit n → n ≡ 0 ⊎ n ≡ 1
bounded O = inj₁ refl
bounded I = inj₂ refl
bounded (x nand y) with bounded x | bounded y
bounded (_nand_ {.0}{.0} x y) | inj₁ refl | inj₁ refl = inj₂ refl
bounded (_nand_ {.0}{.1} x y) | inj₁ refl | inj₂ refl = inj₂ refl
bounded (_nand_ {.1}{.0} x y) | inj₂ refl | inj₁ refl = inj₂ refl
bounded (_nand_ {.1}{.1} x y) | inj₂ refl | inj₂ refl = inj₁ refl

_and_ : ∀ {m n} → Bit m → Bit n → Bit (m b-and n)
_and_ {m}{n} x y rewrite sym (rewriteAnd m n) =
  (x nand y) nand (x nand y)

_xor_ : ∀ {m n} → Bit m → Bit n → Bit (m b-xor n)
_xor_ {m}{n} x y rewrite sym (rewriteXor m n) =
  (x nand (x nand y)) nand (y nand (x nand y))

-- Collections of bits, indexed by their unsigned value.
-- The last bit added is the MSB.
data Bits : ℕ → ℕ → Set where
  [] : Bits 0 0
  _∷_ : ∀ {w m n} (b : Bit m) (bs : Bits w n)
        → Bits (suc w) (2 ^ w * m + n)

-- Split off the MSB of a Bits collection.
split1 : ∀ {w val}
       → (xs : Bits (suc w) val)
       → ∃₂ λ m n → Bit m × Bits w n × (2 ^ w * m + n ≡ val)
split1 (b ∷ bs) with bounded b
split1 (b ∷ bs) | inj₁ refl = _ , _ , b , bs , refl
split1 (b ∷ bs) | inj₂ refl = _ , _ , b , bs , refl










-- Add two bits together.
module HalfAdder where
  adder-spec : ℕ → ℕ → ℕ
  adder-spec m n =
    m and-spec n + (m and-spec n + 0) + (m xor-spec n + 0 + 0)

  implementation : {m n : ℕ}
                 → Bit m → Bit n
                 → Bits 2 (adder-spec m n)
  implementation x y =
    x and y ∷ x xor y ∷ []

  lemma : {m n : ℕ}
        → Bit m → Bit n
        → adder-spec m n ≡ m + n
  lemma x y with bounded x | bounded y
  ... | inj₁ refl | inj₁ refl = refl
  ... | inj₁ refl | inj₂ refl = refl
  ... | inj₂ refl | inj₁ refl = refl
  ... | inj₂ refl | inj₂ refl = refl

  add : {m n : ℕ} → Bit m → Bit n → Bits 2 (m + n)
  add x y = subst (Bits 2) (lemma x y) (implementation x y)








-- Add three bits together.
module FullAdder where
  adder-spec : ℕ → ℕ → ℕ → ℕ
  adder-spec m n o =
    (2 * ((m xor-spec n) nand-spec o) nand-spec (m nand-spec n)) +
    (1 * (m xor-spec n) xor-spec o + 0)

  implementation : {m n o : ℕ}
                 → Bit m → Bit n → Bit o
                 → Bits 2 (adder-spec m n o)
  implementation x y z = (x⊕y nand z) nand (x nand y) ∷ x⊕y xor z ∷ []
    where x⊕y = x xor y

  lemma : {m n o : ℕ}
        → Bit m → Bit n → Bit o
        → adder-spec m n o ≡ m + n + o
  lemma x y z with bounded x | bounded y | bounded z
  ... | inj₁ refl | inj₁ refl | inj₁ refl = refl
  ... | inj₁ refl | inj₁ refl | inj₂ refl = refl
  ... | inj₁ refl | inj₂ refl | inj₁ refl = refl
  ... | inj₁ refl | inj₂ refl | inj₂ refl = refl
  ... | inj₂ refl | inj₁ refl | inj₁ refl = refl
  ... | inj₂ refl | inj₁ refl | inj₂ refl = refl
  ... | inj₂ refl | inj₂ refl | inj₁ refl = refl
  ... | inj₂ refl | inj₂ refl | inj₂ refl = refl

  add : {m n o : ℕ} → Bit m → Bit n → Bit o → Bits 2 (m + n + o)
  add x y z = subst (Bits 2) (lemma x y z) (implementation x y z)









-- Add two n-bit numbers together.
module RippleAdder where
  module Lemma (w : ℕ) where

    -- Proof by reflection!
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



  open ≡-Reasoning

  main-proof
    : (w bx bxs by bys bc bc-sum bsum : ℕ)
    → let 2ʷ = 2 ^ w in
      2ʷ * bc-sum + bsum ≡ bxs + bys + bc
    → 2ʷ * (bx + by + bc-sum) + bsum ≡ 2ʷ * bx + bxs + (2ʷ * by + bys) + bc
  main-proof w bx bxs by bys bc bc-sum bsum lemma =
    let 2ʷ = 2 ^ w in
    begin
      2ʷ * (bx + by + bc-sum) + bsum
                ≡⟨ Lemma.#1 w bc-sum bx by bsum ⟩
      2ʷ * (bx + by) + (2ʷ * bc-sum + bsum)
                ≡⟨ cong (_+_ (2ʷ * (bx + by))) lemma ⟩
      2ʷ * (bx + by) + (bxs + bys + bc)
                ≡⟨ Lemma.#2 w bc bx by bxs bys ⟩
      2ʷ * bx + bxs + (2ʷ * by + bys) + bc ∎

   -- cong : {A B : Set}
   --      → (f : A → B)
   --      → {x y : A}
   --      → x ≡ y → f x ≡ f y



  add : {w m n : ℕ}
      → Bits w m → Bits w n
      → {c : ℕ} → Bit c
      → Bits (1 + w) (m + n + c)
  add {.0} [] [] c with bounded c
  add {.0} [] [] c | inj₁ refl = c ∷ []
  add {.0} [] [] c | inj₂ refl = c ∷ []
  add {suc w} (x ∷ xs) (y ∷ ys) c with split1 (add xs ys c)
  add {suc w} (_∷_ {m = bx} {n = bxs} x xs)
              (_∷_ {m = by} {n = bys} y ys)
              {bc} c
            | bc-sum , bsum , c′ , sum , prf
    -- subst has a type similar to
    -- {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
    = subst (Bits (2 + w))
            (main-proof w bx bxs by bys bc bc-sum bsum prf)
            (collect-bits (FullAdder.add x y c′) sum)
    where
      collect-bits : {bx : ℕ} → Bits 2 bx
                   → {n  : ℕ} → Bits w n
                   → Bits (2 + w) (2 ^ w * bx + n)
      collect-bits (_∷_ {m = bc} c
                        (_∷_ {m = bx}
                             x []))
                   {n} xs =
        subst (Bits (2 + w)) (Lemma.#3 w bc bx n) (c ∷ x ∷ xs)
