module Main where

open import Data.Nat     using (ℕ; _+_)
open import Data.Product using (_,_; _×_; proj₁; proj₂; uncurry)
open import Data.String  using (_++_)
open import Data.Unit    using (⊤)
open import Function     using (_$_)
open import IO           using (IO; putStrLn; run)
open import IO.Primitive using () renaming (IO to PrimIO)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Digital.Bits
open import Digital.Signals
open import Digital.Signature
open import Digital.Adders
open import Digital.Semantics.Show

add = uncurry {C = λ _ → ℕ} _+_

circuit : ∀ {S : ℕ → Set} (s : Signals S)
        → {m,n : ℕ × ℕ}
        → (S (proj₁ m,n) × S (proj₂ m,n))
        → Bits S 2 (add m,n)
circuit s = uncurry $ HalfAdder.add s (defaultSigOps s)

test : show (bit t+ bit) (bits 2) add circuit
       ≡ "((b0 nand b1) nand (b0 nand b1)):" ++
         "((b0 nand (b0 nand b1)) nand (b1 nand (b0 nand b1)))"
test = refl

main′ : IO ⊤
main′ = putStrLn $ show (bit t+ bit) (bits 2) add circuit

main : PrimIO ⊤
main = run main′
