module Digital.Semantics.Graph where

open import Category.Monad.State
  using (State; module RawIMonadState; StateMonadState)
import Data.AVL
open import Data.List    using (List; _∷_; []; _++_; foldr)
open import Data.Maybe   using (maybe)
open import Data.Nat     using (ℕ; suc; zero; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using () renaming (strictTotalOrder to ℕ-STO)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; _$_)
open import Relation.Binary
  using () renaming (StrictTotalOrder to STO)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Digital.Bits
open import Digital.OpSpec
open import Digital.Signals
open import Digital.Signature

private
  open Data.AVL (λ _ → List ℕ) (STO.isStrictTotalOrder ℕ-STO)

  tree-union : Tree → Tree → Tree
  tree-union x = foldr f x ∘ toList
    where
    f : (ℕ × List ℕ) → Tree → Tree
    f (k , v) t =
      insert k (maybe {B = λ _ → List ℕ}
                         (_++_ v)
                         v (lookup k t))
                t

  tree-ex₀ =
    fromList ((0 , []) ∷
              (1 , (0 ∷ [])) ∷
              (2 , (0 ∷ [])) ∷
              [])

  tree-ex₁ =
    fromList ((0 , []) ∷
              (1 , (0 ∷ [])) ∷
              (2 , (1 ∷ [])) ∷
              [])

  tree-ex₂ : tree-union tree-ex₀ tree-ex₁ ≡
    fromList ((0 , []) ∷
              (1 , (0 ∷ 0 ∷ [])) ∷
              (2 , (1 ∷ 0 ∷ [])) ∷
              [])
  tree-ex₂ = refl

  record St : Set where
    constructor st
    field
      n : ℕ
      mapping : Tree

  data Node : ℕ → Set where
    node : {n : ℕ} → (n≤1 : n ≤ 1) → (f : State St ℕ) → Node n

  nodeProof : ∀ {n} → Node n → n ≤ 1
  nodeProof (node n≤1 _) = n≤1

  nodeAction : ∀ {n} → Node n → State St ℕ
  nodeAction (node _ x) = x

  open RawIMonadState (StateMonadState St)

  -- generate a fresh id
  getNext : State St ℕ
  getNext = get >>= λ state → put (f state) >> return (St.n state)
    where
    f : St → St
    f (st n t) = st (suc n) $ tree-union (singleton n []) t

  -- add a link from x to y
  _==>_ : ℕ → ℕ → State St ⊤
  x ==> y = modify f >> return tt
    where
    f : St → St
    f (st n t) = st n $ tree-union (singleton x (y ∷ [])) t

  gnand : ∀ {m n} → Node m → Node n → Node (m b-nand n)
  gnand (node m≤1 x) (node n≤1 y) =
    node (nand-bounded m≤1 n≤1) $
         x       >>= λ a →
         y       >>= λ b →
         getNext >>= λ c →
         c ==> a >>
         c ==> b >>
         return c

  gbind : ∀ {ni no}
        → (ti : Ty ni) (ixi : IX⟦ ti ⟧)
        → (to : Ty no) (ixo : IX⟦ to ⟧)
        → T⟦ Node ∣ ti ∶ ixi ⟧
        → S⟦ Node ∣ ti ∶ ixi ↦ to ∶ ixo ⟧
        → T⟦ Node ∣ to ∶ ixo ⟧
  gbind bit ixi bit ixo (node ixi≤1 x) f =
    node ixo≤1 (run >>= return ∘ proj₂)
    where go : Node ixo → State St (ixo ≤ 1 × ℕ)
          go (node ixo≤1 y) = y >>= (return ∘ _,_ ixo≤1)
          run   = x >>= λ i → go $ f (node ixi≤1 $ return i)
          ixo≤1 = proj₁ $ (run >>= return ∘ proj₁) $ st 0 empty
  gbind bit ixi (bits 0) ixo (node ixi≤1 x) f = {!!}
  gbind bit ixi (bits (suc n)) ixo x f = {!!}
  gbind bit ixi (x t+ y) (ixo₁ , ixo₂) (node ixi≤1 m) f = {!!} , {!!}
  gbind (bits w) ixi to ixo x f = {!!}
  gbind (x t+ y) (ixi₁ , ixi₂) to ixo x' f = {!!}

  gbounded : ∀ {n} → Node n → n ≡ 0 ⊎ n ≡ 1
  gbounded (node      z≤n  _) = inj₁ refl
  gbounded (node (s≤s z≤n) _) = inj₂ refl

  signals : Signals Node
  signals = record
    { _nand_  = gnand
    ; bind    = gbind
    ; O       = node z≤n getNext
    ; I       = node (s≤s z≤n) getNext
    ; bounded = gbounded
    }

  genVars : ∀ {n} (ty : Ty n) → State St T⟦ Node ∣ ty ∶ ixZero ty ⟧
  genVars  bit = getNext >>= λ i → return $ node z≤n (return i)
  genVars (bits zero) = return []
  genVars (bits (suc w)) = {!!}
  genVars (x t+ y) =
    genVars x >>= λ xv →
    genVars y >>= λ yv →
    return (xv , yv)

  graphT : ∀ {n}
         → (ty : Ty n)
         → {ix : IX⟦ ty ⟧}
         → T⟦ Node ∣ ty ∶ ix ⟧
         → State St ⊤
  graphT bit x with nodeAction x
  ... | nx = nx >>= λ n → return tt
  graphT (bits w) x =
    {!!}
  graphT (tx t+ ty) (x , y) =
    graphT tx x >>= λ gx →
    graphT ty y >>= λ gy →
    return tt

graph : ∀ {ni no}
      → (ti : Ty ni) (to : Ty no)
      → (ixFn : IX⟦ ti ⟧ → IX⟦ to ⟧)
      → (∀ {S : ℕ → Set} (s : Signals S) {ix : IX⟦ ti ⟧}
         → S⟦ S ∣ ti ∶ ix ↦ to ∶ ixFn ix ⟧)
      → List (ℕ × List ℕ)
graph ti to ixFn f = toList ∘ St.mapping ∘ proj₂ $ go (st 0 empty)
  where
  go = genVars ti >>= (graphT to ∘ f signals)

private
  ex₀ : graph bit bit defNot
              (λ s x → let open SigOps (defaultSigOps s)
                           open Utilities s
                       in bind1-1 x (λ o → o nand o))
      ≡ (0 , []) ∷ (1 , 0 ∷ 0 ∷ []) ∷ []
  ex₀ = refl

  ex₁ : graph bit (bit t+ bit) (λ i → defNot i , defNot i)
              (λ s x → let open SigOps (defaultSigOps s)
                       in bind bit _ (bit t+ bit) _ x
                          (λ o → o nand o , o nand o))
      ≡ (0 , []) ∷ (1 , 0 ∷ 0 ∷ []) ∷ (2 , 0 ∷ 0 ∷ []) ∷ []
  ex₁ = {!!}