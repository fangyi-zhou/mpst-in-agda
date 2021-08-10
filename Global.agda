open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Common using (Role; Label; Action; AMsg)

data Global : Set where
    End : Global
    MsgSingle : (p q : Role) -> ¬ (p ≡ q) -> Label -> Global -> Global

data _-_→ᵍ_ : Global -> Action -> Global -> Set where
    GPrefix : ∀{p q l g' p≠q} -> (MsgSingle p q p≠q l g') - (AMsg p q l) →ᵍ g'
    GCont : ∀{p q l l' r s g₁ g₂ r≠s}
        -> g₁ - (AMsg p q l) →ᵍ g₂
        -> ¬ (p ≡ r)
        -> ¬ (q ≡ r)
        -> ¬ (p ≡ s)
        -> ¬ (q ≡ s)
        -> (MsgSingle r s r≠s l' g₁) - (AMsg p q l) →ᵍ (MsgSingle r s r≠s l' g₂)
