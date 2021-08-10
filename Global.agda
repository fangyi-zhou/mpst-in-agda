open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Common using (Role; Label)

data Global : Set where
    End : Global
    MsgSingle : (p q : Role) -> ¬ (p ≡ q) -> Label -> Global -> Global
