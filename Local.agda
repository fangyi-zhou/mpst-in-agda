open import Relation.Binary.PropositionalEquality using (subst; _≡_)
open import Relation.Nullary using (¬_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup; _[_]≔_)

open import Common using (Label; Action; action)

data Local (n : ℕ) : Set where
    endL : Local n
    sendSingle recvSingle : Fin n -> Label -> Local n -> Local n

Configuration : ℕ -> Set
Configuration n = Vec (Local n) n

data _-_→l_ {n : ℕ} : Local n -> Action n -> Local n -> Set where
    →l-send :
        ∀ { q lbl lt' }
        -> (p : Fin n)
        -> (p≠q : ¬ (p ≡ q))
        -> sendSingle q lbl lt' - (action p q p≠q lbl) →l lt'
    →l-recv :
        ∀ { q lbl lt' }
        -> (p : Fin n)
        -> (q≠p : ¬ (q ≡ p))
        -> recvSingle q lbl lt' - (action q p q≠p lbl) →l lt'

data _-_→c_ {n : ℕ} : Configuration n -> Action n -> Configuration n -> Set where
    →c-comm :
        ∀ { p q l lp lp' lq lq' c' }
        -> (c : Configuration n)
        -> (p≠q : ¬ (p ≡ q))
        -> (lp ≡ lookup c p)
        -> (lq ≡ lookup c q)
        -> (c' ≡ (c [ p ]≔ lp') [ q ]≔ lq')
        -> lp - (action p q p≠q l) →l lp'
        -> lq - (action p q p≠q l) →l lq'
        -> c - (action p q p≠q l) →c  c'
