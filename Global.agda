open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary using (DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List using (List; []; _∷_; deduplicate)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.Unique.Setoid using (Unique)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Nat.Properties using (≡-decSetoid)
open import Data.List.Membership.DecSetoid ≡-decSetoid using (_∈?_)
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

roles : Global -> List Role
roles End = []
roles (MsgSingle p q _ _ g') with p ∈? roles g' | q ∈? roles g'
...                              | yes _        | yes _         = roles g'
...                              | no _         | yes _         = p ∷ roles g'
...                              | yes _        | no _          = q ∷ roles g'
...                              | no _         | no _          = p ∷ q ∷ roles g'

roles-unique : (g : Global) -> Unique (DecSetoid.setoid ≡-decSetoid) (roles g)
roles-unique End = AllPairs.[]
roles-unique g@(MsgSingle p q p≠q _ g') with p ∈? roles g' | q ∈? roles g'
...                                      | yes _         | yes _         = roles-unique g'
...                                      | no p∉         | yes _         = ¬Any⇒All¬ (roles g') p∉ AllPairs.∷ roles-unique g'
...                                      | yes _         | no q∉         = ¬Any⇒All¬ (roles g') q∉ AllPairs.∷ roles-unique g'
...                                      | no p∉         | no q∉         = (p≠q All.∷ ¬Any⇒All¬ (roles g') p∉) AllPairs.∷ ¬Any⇒All¬ (roles g') q∉ AllPairs.∷ roles-unique g'
