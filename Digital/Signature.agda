{-# OPTIONS --universe-polymorphism #-}

open import Data.Nat

module Digital.Signature where

open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Vec

open import Digital.Bits

infixr 4 _t+_
data Ty : (nArgs : ℕ) → Set where
  bit  : Ty 1
  bits : (w : ℕ) → Ty 1
  _t+_  : ∀ {m n} → (x : Ty m) → (y : Ty n) → Ty (m + n)

IX⟦_⟧ : ∀ {n} → Ty n → Set
IX⟦ bit    ⟧ = ℕ
IX⟦ bits w ⟧ = ℕ
IX⟦ x t+ y ⟧ = IX⟦ x ⟧ × IX⟦ y ⟧

T⟦_∣_∶_⟧ : ∀ {n} → (Bit  : ℕ → Set) → (ty : Ty n) → IX⟦ ty ⟧ → Set
T⟦ Bit ∣ bit    ∶ n ⟧         = Bit n
T⟦ Bit ∣ bits w ∶ n ⟧         = Bits Bit w n
T⟦ Bit ∣ x t+ y ∶ (ix , iy) ⟧ = T⟦ Bit ∣ x ∶ ix ⟧ × T⟦ Bit ∣ y ∶ iy ⟧

ixZero : ∀ {n} → (ty : Ty n) → IX⟦ ty ⟧
ixZero  bit     = 0
ixZero (bits w) = 0
ixZero (x t+ y) = ixZero x , ixZero y

data Sig : ℕ → ℕ → Set where
  _∶_↦_∶_ : ∀ {bi bo}
            → (ti : Ty bi) (ii : IX⟦ ti ⟧)
            → (to : Ty bo) (io : IX⟦ to ⟧)
            → Sig bi bo

S⟦_∣_⟧ : ∀ {m n} → (Bit  : ℕ → Set) → Sig m n → Set
S⟦ Bit ∣ i ∶ ii ↦ o ∶ io ⟧  = T⟦ Bit ∣ i ∶ ii ⟧ → T⟦ Bit ∣ o ∶ io ⟧
