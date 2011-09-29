module Digital.NatExtra where

open import Algebra
open import Data.Nat as N
import Data.Nat.Properties as N
open N.SemiringSolver using (solve; _:+_; _:*_; _:=_; con)
open import Data.Nat.Properties using (_+-mono_; m≤m+n)
open import Data.Product
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
  module CS = CommutativeSemiring N.commutativeSemiring
  module DTO = DecTotalOrder N.decTotalOrder
  open ≤-Reasoning renaming (begin_ to start_; _∎ to _□; _≡⟨_⟩_ to _≡⟨_⟩'_)
  open ≡-Reasoning

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ 0 = 1
x ^ (suc e) = x * (x ^ e)

+-congˡ : ∀ {x y} n → x ≡ y → n + x ≡ n + y
+-congˡ n = cong (λ x → n + x)

+-congʳ : ∀ {x y} n → x ≡ y → x + n ≡ y + n
+-congʳ n = cong (λ x → x + n)

+-identʳ = proj₂ CS.+-identity

-- 0 * n or 1 * n is no greater than n.
m≤1→m*n≤n : ∀ {m : ℕ} → m ≤ 1 → (n : ℕ) → m * n ≤ n
m≤1→m*n≤n {.0}      z≤n  _ = z≤n
m≤1→m*n≤n {.1} (s≤s z≤n) n rewrite CS.+-comm n 0 = DTO.refl

1≤2ⁿ : ∀ n → 1 ≤ 2 ^ n
1≤2ⁿ zero = s≤s z≤n
1≤2ⁿ (suc n) =
  start 1                 ≤⟨ 1≤2ⁿ n ⟩
        2 ^ n             ≤⟨ m≤m+n (2 ^ n) (2 ^ n + 0) ⟩
        2 ^ n + (2 ^ n + 0) □

n<2¹⁺ⁿ : ∀ n → n < 2 ^ (1 + n)
n<2¹⁺ⁿ zero = s≤s z≤n
n<2¹⁺ⁿ (suc n) =
  let 2ⁿ = 2 ^ n; 2ⁿ+_ = _+_ 2ⁿ; _+0 = flip _+_ 0 in
  start 1 + n
     <⟨ _+-mono_ {1} (DTO.reflexive refl) (n<2¹⁺ⁿ n) ⟩
        1 + (2ⁿ + (2ⁿ + 0))
     ≤⟨ 1≤2ⁿ n +-mono DTO.reflexive refl ⟩
        2ⁿ + (2ⁿ + (2ⁿ + 0))
     ≡⟨ solve 1 (λ x → x :+ (x :+ (x :+ con 0)) := x :+ x :+ x :+ con 0)
              refl 2ⁿ ⟩'
        2ⁿ + 2ⁿ + 2ⁿ + 0
     ≤⟨ _+-mono_ {2ⁿ + 2ⁿ + 2ⁿ} (DTO.reflexive refl) z≤n ⟩
        2ⁿ + 2ⁿ + 2ⁿ + 2ⁿ
     ≡⟨ solve 1 (λ x → x :+ x :+ x :+ x
                    := x :+ (x :+ con 0) :+ (x :+ (x :+ con 0) :+ con 0))
              refl 2ⁿ ⟩'
        2 ^ (2 + n) □

swapSuc : ∀ m n → m + (1 + n) ≡ 1 + m + n
swapSuc zero n = refl
swapSuc (suc m) n = cong suc (swapSuc m n)

0≡n∸n : ∀ n → 0 ≡ n ∸ n
0≡n∸n n =
  begin 0
    ≡⟨ sym (N.m+n∸n≡m 0 n) ⟩
        (0 + n) ∸ n
    ≡⟨ refl ⟩
        n ∸ n ∎

m∸n≡0⇒m≡n : ∀ {m n} → m ∸ n ≡ 0 → m ≤ n
m∸n≡0⇒m≡n {m} {zero} p = DTO.reflexive p
m∸n≡0⇒m≡n {zero} {suc n} p = z≤n
m∸n≡0⇒m≡n {suc n} {suc n'} p = s≤s (m∸n≡0⇒m≡n p)

sn∸sm≡n∸m : ∀ {n m} → m < n → suc (n ∸ suc m) ≡ n ∸ m
sn∸sm≡n∸m {.(suc n)}  {zero} (s≤s       {.0} {n} m≤n) = refl
sn∸sm≡n∸m {.(suc n)} {suc m} (s≤s {.(suc m)} {n} m≤n) = sn∸sm≡n∸m m≤n

≤-step′ : ∀ {m n} → suc m ≤ n → m ≤ n
≤-step′ {m} {.(suc n)} (s≤s {.m} {n} m≤n) = N.≤-step m≤n
