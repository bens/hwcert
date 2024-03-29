module Digital.Semantics.Show where

open import Algebra using (module CommutativeSemiring)
open import Category.Monad.State
  using (State; module RawIMonadState; StateMonadState)
open import Data.Bool           using (true; false)
open import Data.Nat            using (ℕ; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (commutativeSemiring)
open import Data.Nat.Show       using () renaming (show to ℕ-show)
open import Data.Product        using (_,_; proj₁)
open import Data.String         using (String; _++_; _==_)
open import Data.Sum            using (_⊎_; inj₁; inj₂)
open import Function            using (_$_; _∘_; flip; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst)

open import Digital.Bits
open import Digital.Signature
open import Digital.OpSpec
open import Digital.Signals
open import Digital.NatExtra as ℕ-E using (_^_)

open CommutativeSemiring commutativeSemiring using (+-comm; *-comm)
open RawIMonadState (StateMonadState ℕ)

private
  data Var : ℕ → Set where
    var : ∀ {n} → (n≤1 : n ≤ 1) → String → Var n

  snand : ∀ {m n} → Var m → Var n → Var (m b-nand n)
  snand {m}{n} (var px x) (var py y) =
    var (nand-bounded px py) $ "(" ++ x ++ " nand " ++ y ++ ")"

  sbind : ∀ {ni no}
        → (ti : Ty ni) (ixi : IX⟦ ti ⟧)
        → (to : Ty no) (ixo : IX⟦ to ⟧)
        → T⟦ Var ∣ ti ∶ ixi ⟧
        → S⟦ Var ∣ ti ∶ ixi ↦ to ∶ ixo ⟧
        → T⟦ Var ∣ to ∶ ixo ⟧
  sbind _ _ _ _ x f = f x

  sbounded : ∀ {n} → Var n → n ≡ 0 ⊎ n ≡ 1
  sbounded (var      z≤n  _) = inj₁ refl
  sbounded (var (s≤s z≤n) _) = inj₂ refl

  signals : Signals Var
  signals = record
    { _nand_  = snand
    ; bind    = sbind
    ; O       = var z≤n "O"
    ; I       = var (s≤s z≤n) "I"
    ; bounded = sbounded
    }

  showVar : ∀ {n} → Var n → String
  showVar (var _ xs) = xs

  showBits : ∀ {w n} → Bits Var w n → String
  showBits = go ""
    where
    go : ∀ {w n} → String → Bits Var w n → String
    go ss [] = ss
    go ss (b ∷ bs) with ss == ""
    ... | true  = go (showVar b) bs
    ... | false = go (ss ++ ":" ++ showVar b) bs

  showT : ∀ {n} → (ty : Ty n) {ix : IX⟦ ty ⟧} → T⟦ Var ∣ ty ∶ ix ⟧ → String
  showT  bit x          = showVar x
  showT (bits w) x      = showBits x
  showT (t , u) (x , y) = showT t x ++ ", " ++ showT u y

  nextI : State ℕ ℕ
  nextI = get >>= λ i → put (1 + i) >> return i

  genVars : ∀ {n} (ty : Ty n) → State ℕ T⟦ Var ∣ ty ∶ ixZero ty ⟧
  genVars  bit     = nextI >>= λ i → return $ var z≤n ("b" ++ ℕ-show i)
  genVars (bits 0) = return []
  genVars (bits (suc w)) =
    let lemma = cong (flip _+_ 0) $ *-comm (2 ^ w) 0
    in genVars (bits w) >>= λ vs →
       nextI            >>= λ i →
       return $ subst (Bits Var (suc w)) lemma
                      (var z≤n ("bs" ++ ℕ-show i) ∷ vs)
  genVars (x , y) =
    genVars x >>= λ tx → genVars y >>= λ ty → return (tx , ty)

show : ∀ {ni no}
     → (ti : Ty ni) (to : Ty no)
     → (ixFn : IX⟦ ti ⟧ → IX⟦ to ⟧)
     → (∀ {S : ℕ → Set} (s : Signals S) {ix : IX⟦ ti ⟧}
        → S⟦ S ∣ ti ∶ ix ↦ to ∶ ixFn ix ⟧)
     → String
show x y _ f = showT y ∘ f signals ∘ proj₁ $ genVars x 0

private
  test₀ : show bit bit id (λ s → id) ≡ "b0"
  test₀ = refl

  test₁ : show bit bit defNot (λ s x → let open Signals s in x nand x)
          ≡ "(b0 nand b0)"
  test₁ = refl

  test₂ : show bit bit defNot
            (λ s x → let open Signals s; open Utilities s in
                     bind1-1 x $ λ o → o nand o)
          ≡ "(b0 nand b0)"
  test₂ = refl

  test₃-fn : ∀ {S : ℕ → Set} (s : Signals S) {n : ℕ} → Bits S 1 n → S n
  test₃-fn s (_∷_ {.0}{m}{.0} b [])
    rewrite +-comm (m + 0) 0 | +-comm m 0 = b

  test₃ : show (bits 1) bit id test₃-fn ≡ "bs0"
  test₃ = refl

  test₄-fn : ∀ {S : ℕ → Set} (s : Signals S) {n : ℕ} → S n → Bits S 2 n
  test₄-fn {S} s {n} = go {n}
    where open Signals s
          go : {n : ℕ} → S n → Bits S 2 n
          go { n} x with bounded x
          go {.0} x | inj₁ refl = O ∷ x ∷ []
          go {.1} x | inj₂ refl = O ∷ x ∷ []

  test₄ : show bit (bits 2) id test₄-fn ≡ "O:b0"
  test₄ = refl
