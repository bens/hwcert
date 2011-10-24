{-# OPTIONS --universe-polymorphism #-}

module Digital.Adders where

open import Data.Nat            using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (module SemiringSolver)
open import Data.Product        using (_×_; _,_; uncurry)
open import Data.Sum            using (inj₁; inj₂)
open import Data.Vec            using (_∷_; [])
open import Function            using (_$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

-- local
import Digital.Bits
import Digital.Bits.Properties
open import Digital.NatExtra using (_^_)
open import Digital.OpSpec
import Digital.Signals
import Digital.Signature

module HalfAdder
    {Bit : ℕ → Set}
    (signals : Digital.Signals.Signals Bit)
    (sigops : Digital.Signals.SigOps signals)
    where

  open Digital.Bits Bit
  open Digital.Signals.SigOps sigops
  open Digital.Signature

  implSpec = λ (m n : ℕ)
             → (m b-and n + (m b-and n + 0) + (m b-xor n + 0 + 0))

  private
    impl : ∀ {m n} → Bit m × Bit n → Bits 2 (implSpec m n)
    impl (x , y) = x and y ∷ x xor y ∷ []

  add : ∀ {m n} → Bit m → Bit n → Bits 2 (m + n)
  add {m}{n} x y =
    subst (Bits 2) (p x y) $
      bind (bit t+ bit) _ (bits 2) _ (x , y) impl
    where
    p : ∀ {m n} → Bit m → Bit n → implSpec m n ≡ m + n
    p x y with bounded x | bounded y
    ...      | inj₁ refl | inj₁ refl = refl
    ...      | inj₁ refl | inj₂ refl = refl
    ...      | inj₂ refl | inj₁ refl = refl
    ...      | inj₂ refl | inj₂ refl = refl

module FullAdder
    {Bit : ℕ → Set}
    (signals : Digital.Signals.Signals Bit)
    (sigops : Digital.Signals.SigOps signals)
    where

  open Digital.Bits Bit
  open Digital.Signals.Utilities signals
  open Digital.Signals.SigOps sigops
  open Digital.Signature

  implSpec = λ (m n o : ℕ)
             → (2 * ((m b-xor n) b-nand o) b-nand (m b-nand n))
             + (1 * (m b-xor n) b-xor o + 0)

  private
    impl : ∀ {m n o} → Bit m × Bit n × Bit o → Bits 2 (implSpec m n o)
    impl (x , y , z) =
      bind1-n (x xor y) $
        λ x⊗y → (x⊗y nand z) nand (x nand y) ∷ x⊗y xor z ∷ []

  add : ∀ {m n o} → Bit m → Bit n → Bit o → Bits 2 (m + n + o)
  add {m}{n}{o} x y z =
    subst (Bits 2) (p x y z) $
      bind (bit t+ bit t+ bit) _ (bits 2) _ (x , y , z) impl
    where
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
    {Bit : ℕ → Set}
    (signals : Digital.Signals.Signals Bit)
    (sigops : Digital.Signals.SigOps signals)
    where

  open Digital.Bits Bit                    using (Bits; []; _∷_)
  open Digital.Bits.Properties Bit signals using (split1)
  open Digital.Signals.SigOps sigops       using (bounded)

  private
    module Lemma (w : ℕ) where
      open SemiringSolver using (solve; _:+_; _:*_; _:=_; con)
      2ʷ = 2 ^ w

      #1 : ∀ bc bx by bxs bys
           → (2ʷ * bx + bxs) + (2ʷ * by + bys) + bc
           ≡ 2ʷ * (bx + by) + (bxs + bys + bc)
      #1 bc bx by bxs bys =
        solve 6 (λ 2ʷ' bx' bxs' by' bys' bc'
                 → 2ʷ' :* bx' :+ bxs' :+ (2ʷ' :* by' :+ bys') :+ bc'
                := 2ʷ' :* (bx' :+ by') :+ (bxs' :+ bys' :+ bc'))
              refl 2ʷ bx bxs by bys bc

      #2 : ∀ bc bx by n
           → 2ʷ * (bx + by) + (2ʷ * bc + n)
           ≡ 2ʷ * (bx + by + bc) + n
      #2 bc bx by n =
        solve 5 (λ 2ʷ' bc' bx' by' n'
                 → 2ʷ' :* (bx' :+ by') :+ (2ʷ' :* bc' :+ n')
                := 2ʷ' :* (bx' :+ by' :+ bc') :+ n')
              refl 2ʷ bc bx by n

      #3 : ∀ bc bx n
           → 2ʷ * (2 * bc + (1 * bx + 0)) + n
           ≡ (2 ^ (1 + w) * bc) + (2ʷ * bx + n)
      #3 bx bc val =
        solve 4 (λ 2ʷ' bx' bc' val'
                 → let 0' = con 0 in
                   2ʷ' :* (bc' :+ (bc' :+ 0') :+ (bx' :+ 0' :+ 0')) :+ val'
                := (2ʷ' :+ (2ʷ' :+ 0')) :* bc' :+ (2ʷ' :* bx' :+ val'))
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
    rewrite Lemma.#1 w bc bx by bxs bys
          | sym prf
          | Lemma.#2 w bc′ bx by bsum
          = go (FullAdder.add signals sigops x y c′) sum
    where
    go : ∀ {bx n} → Bits 2 bx → Bits w n → Bits (2 + w) (2 ^ w * bx + n)
    go {._}{n} (_∷_ {m = bc} c (_∷_ {m = bx} x [])) xs
      rewrite Lemma.#3 w bc bx n = c ∷ x ∷ xs
