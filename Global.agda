open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

open import Common using (Label; Action; action)

data Global (n : ℕ) : Set where
    endG : Global n
    msgSingle : (p q : Fin n) -> ¬ (p ≡ q) -> Label -> Global n -> Global n

data _-_→g_ {n : ℕ} : Global n -> Action n -> Global n -> Set where
    →g-prefix :
        ∀ { p q l g' p≠q }
        -> (msgSingle p q p≠q l g') - (action p q p≠q l) →g g'
    →g-cont :
        ∀ { p q l l' r s g₁ g₂ p≠q r≠s }
        -> g₁ - (action p q p≠q l) →g g₂
        -> ¬ (p ≡ r)
        -> ¬ (q ≡ r)
        -> ¬ (p ≡ s)
        -> ¬ (q ≡ s)
        -> (msgSingle r s r≠s l' g₁) - (action p q p≠q l) →g (msgSingle r s r≠s l' g₂)
