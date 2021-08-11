open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Common using (Role; Label; Action; AMsg)

data Global : Set where
    End : Global
    MsgSingle : (p q : Role) -> ¬ (p ≡ q) -> Label -> Global -> Global

data _-_→g_ : Global -> Action -> Global -> Set where
    GPrefix : ∀{p q l g' p≠q} -> (MsgSingle p q p≠q l g') - (AMsg p q p≠q l) →g g'
    GCont : ∀{p q l l' r s g₁ g₂ p≠q r≠s}
        -> g₁ - (AMsg p q p≠q l) →g g₂
        -> ¬ (p ≡ r)
        -> ¬ (q ≡ r)
        -> ¬ (p ≡ s)
        -> ¬ (q ≡ s)
        -> (MsgSingle r s r≠s l' g₁) - (AMsg p q p≠q l) →g (MsgSingle r s r≠s l' g₂)
