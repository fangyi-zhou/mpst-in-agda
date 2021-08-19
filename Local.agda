open import Relation.Binary.PropositionalEquality using (subst; _≡_)
open import Relation.Nullary using (¬_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup; _[_]≔_)

open import Common using (Label; Action; AMsg)

data Local (n : ℕ) : Set where
    End : Local n
    Send Recv : Fin n -> Label -> Local n -> Local n

Configuration : ℕ -> Set
Configuration n = Vec (Local n) n

data _-_→l_ {n : ℕ} : Local n -> Action n -> Local n -> Set where
    LSend : ∀{q lbl lt'}
             -> (p : Fin n)
             -> (p≠q : ¬ (p ≡ q))
             -> Send q lbl lt' - (AMsg p q p≠q lbl) →l lt'
    LRecv : ∀{q lbl lt'}
             -> (p : Fin n)
             -> (q≠p : ¬ (q ≡ p))
             -> Recv q lbl lt' - (AMsg q p q≠p lbl) →l lt'

data _-_→c_ {n : ℕ} : Configuration n -> Action n -> Configuration n -> Set where
    CComm : ∀{p q l lp' lq'}
             -> (c : Configuration n)
             -> (p≠q : ¬ (p ≡ q))
             -> lookup c p - (AMsg p q p≠q l) →l lp'
             -> lookup c q - (AMsg p q p≠q l) →l lq'
             -> c - (AMsg p q p≠q l) →c ((c [ p ]≔ lp') [ q ]≔ lq')
