open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)

open import Common using (Label; Action; AMsg)

data Global (n : ℕ) : Set where
    End : Global n
    MsgSingle : (p q : Fin n) -> ¬ (p ≡ q) -> Label -> Global n -> Global n

data _-_→g_ {n : ℕ} : Global n -> Action n -> Global n -> Set where
    GPrefix : ∀{p q l g' p≠q} -> (MsgSingle p q p≠q l g') - (AMsg p q p≠q l) →g g'
    GCont : ∀{p q l l' r s g₁ g₂ p≠q r≠s}
        -> g₁ - (AMsg p q p≠q l) →g g₂
        -> ¬ (p ≡ r)
        -> ¬ (q ≡ r)
        -> ¬ (p ≡ s)
        -> ¬ (q ≡ s)
        -> (MsgSingle r s r≠s l' g₁) - (AMsg p q p≠q l) →g (MsgSingle r s r≠s l' g₂)
