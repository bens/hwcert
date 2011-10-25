module Main where

open import Data.Nat     using (ℕ; _+_)
open import Data.Product using (_,_; _×_; proj₁; proj₂; uncurry)
open import Data.String  using (_++_)
open import Data.Unit    using (⊤)
open import IO           using (IO; putStrLn; run)
open import IO.Primitive using () renaming (IO to PrimIO)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Digital.Bits
open import Digital.Signals
open import Digital.Signature
open import Digital.Adders
open import Digital.Semantics.Show

circuit : ∀ {S : ℕ → Set} (s : Signals S)
        → {n : ℕ × ℕ}
        → (S (proj₁ n) × S (proj₂ n))
        → Bits S 2 (proj₁ n + proj₂ n)
circuit s (x , y) = HalfAdder.add s (defaultSigOps s) x y

test : show (bit t+ bit) (bits 2) (uncurry _+_) circuit
       ≡ "((b0 nand b1) nand (b0 nand b1)):" ++
         "((b0 nand (b0 nand b1)) nand (b1 nand (b0 nand b1)))"
test = refl

main′ : IO ⊤
main′ = putStrLn (show (bit t+ bit) (bits 2)
                       (λ n → proj₁ n + proj₂ n)
                       circuit)

main : IO.Primitive.IO ⊤
main = run main′
