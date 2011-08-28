{-# OPTIONS --universe-polymorphism #-}

module Adders where

open import Data.Nat            using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (module SemiringSolver)
open import Data.Product        using (_,_)
open import Data.Sum            using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

-- local
import Bits hiding (bounded)
open import NatExtra using (_^_)
open import OpSpec
open import Signals

module HalfAdder
    {ℓ} {Bit : ℕ → Set ℓ}
    {signals : Signals Bit}
    (sigops : SigOps signals)
    where

  open Bits signals
  open SigOps sigops

  implSpec = λ (m n : ℕ)
             → (m b-and n + (m b-and n + 0) + (m b-xor n + 0 + 0))

  add : ∀ {m n} → Bit m → Bit n → Bits 2 (m + n)
  add {m}{n} x y = subst (Bits 2) (p x y) (x and y ∷ x xor y ∷ [])
    where
    p : ∀ {m n} → Bit m → Bit n → implSpec m n ≡ m + n
    p x y with bounded x | bounded y
    ...      | inj₁ refl | inj₁ refl = refl
    ...      | inj₁ refl | inj₂ refl = refl
    ...      | inj₂ refl | inj₁ refl = refl
    ...      | inj₂ refl | inj₂ refl = refl

module FullAdder
    {ℓ} {Bit : ℕ → Set ℓ}
    {signals : Signals Bit}
    (sigops : SigOps signals)
    where

  open Bits signals
  open SigOps sigops

  implSpec = λ (m n o : ℕ)
             → (2 * ((m b-xor n) b-nand o) b-nand (m b-nand n))
             + (1 * (m b-xor n) b-xor o + 0)

  add : ∀ {m n o} → Bit m → Bit n → Bit o → Bits 2 (m + n + o)
  add {m}{n}{o} x y z = subst (Bits 2) (p x y z) (carry ∷ x⊗y⊗z ∷ [])
    where
    x⊗y = (x xor y)
    x⊗y⊗z = x⊗y xor z
    carry = (x⊗y nand z) nand (x nand y)
    p : ∀ {m n o} → Bit m → Bit n → Bit o → implSpec m n o ≡ m + n + o
    p x y z with bounded x | bounded y | bounded z
    ...        | inj₁ refl | inj₁ refl | inj₁ refl = refl
    ...        | inj₁ refl | inj₁ refl | inj₂ refl = refl
    ...        | inj₁ refl | inj₂ refl | inj₁ refl = refl
    ...        | inj₁ refl | inj₂ refl | inj₂ refl = refl
    ...        | inj₂ refl | inj₁ refl | inj₁ refl = refl
    ...        | inj₂ refl | inj₁ refl | inj₂ refl = refl
    ...        | inj₂ refl | inj₂ refl | inj₁ refl = refl
    ...        | inj₂ refl | inj₂ refl | inj₂ refl = refl

module RippleAdder
    {ℓ} {Bit : ℕ → Set ℓ}
    {signals : Signals Bit}
    (sigops : SigOps signals)
    where

  open Bits      signals using (Bits; []; _∷_; split1)
  open SigOps    sigops  using (bounded)
  open FullAdder sigops  using () renaming (add to fullAdd)

  private
    module Lemma (w : ℕ) where
      open SemiringSolver using (solve; _:+_; _:*_; _:=_; con)
      2ʷ = 2 ^ w

      №1 : ∀ bc bx by bxs bys
           → (2ʷ * bx + bxs) + (2ʷ * by + bys) + bc
           ≡ 2ʷ * (bx + by) + (bxs + bys + bc)
      №1 bc bx by bxs bys =
        solve 6 (λ 2ʷ' bx' bxs' by' bys' bc'
                → 2ʷ' :* bx' :+ bxs' :+ (2ʷ' :* by' :+ bys') :+ bc'
               := 2ʷ' :* (bx' :+ by') :+ (bxs' :+ bys' :+ bc'))
              refl 2ʷ bx bxs by bys bc

      №2 : ∀ bc bx by n
           → 2ʷ * (bx + by) + (2ʷ * bc + n)
           ≡ 2ʷ * (bx + by + bc) + n
      №2 bc bx by n =
        solve 5 (λ 2ʷ' bc' bx' by' n'
                 → 2ʷ' :* (bx' :+ by') :+ (2ʷ' :* bc' :+ n')
                := 2ʷ' :* (bx' :+ by' :+ bc') :+ n')
              refl 2ʷ bc bx by n

      №3 : ∀ bc bx n
           → 2ʷ * (2 * bx + (1 * bc + 0)) + n
           ≡ (2 ^ (1 + w) * bx) + (2ʷ * bc + n)
      №3 bc bx val =
        solve 4 (λ 2ʷ' bc' bx' val'
                 → let 0' = con 0 in
                   2ʷ' :* (bx' :+ (bx' :+ 0') :+ (bc' :+ 0' :+ 0')) :+ val'
                := (2ʷ' :+ (2ʷ' :+ 0')) :* bx' :+ (2ʷ' :* bc' :+ val'))
              refl 2ʷ bc bx val

  add : ∀ {w m n c}
        → Bits w m → Bits w n → Bit c → Bits (suc w) (m + n + c)
  add {.0} [] [] c with bounded c
  add {.0} [] [] c    | inj₁ refl = c ∷ []
  add {.0} [] [] c    | inj₂ refl = c ∷ []
  add {suc w} {c = bc}
      (_∷_ {.w} {bx} {bxs} x xs) (_∷_ {.w} {by} {bys} y ys) c
       with split1 (add xs ys c)
  ... | bc′ , bsum , c′ , sum , prf
    rewrite Lemma.№1 w bc bx by bxs bys
          | sym prf
          | Lemma.№2 w bc′ bx by bsum
          = go (fullAdd x y c′) sum
    where
    go : ∀ {bx n} → Bits 2 bx → Bits w n → Bits (2 + w) (2 ^ w * bx + n)
    go {._}{n} (_∷_ {m = bx} x (_∷_ {m = bc} c [])) xs
      rewrite Lemma.№3 w bc bx n = x ∷ c ∷ xs
