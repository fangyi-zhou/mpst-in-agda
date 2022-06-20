{-# OPTIONS --guardedness #-}

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)

open import Common

data Global (n : ℕ) : Set
record ∞Global (n : ℕ) : Set

data Global n where
  endG : Global n
  msgSingle : (p q : Fin n) -> p ≢ q -> Label -> ∞Global n -> Global n

record ∞Global n where
  coinductive
  constructor box
  field force : Global n
open ∞Global public

private
  variable
    n : ℕ
    p p′ q q′ r s : Fin n
    p≢q : p ≢ q
    l l′ : Label
    g gSub gSub′ : Global n
    ∞g ∞gSub ∞gSub′ : ∞Global n

msgSingle′ : (p q : Fin n) -> {False (p ≟ q)} -> Label -> ∞Global n -> Global n
msgSingle′ p q {p≢q} l gSub = msgSingle p q (toWitnessFalse p≢q) l gSub

data _∈_ : (r : Fin n) -> (g : Global n) -> Set
data _∞∈_ : (r : Fin n) -> (g : ∞Global n) -> Set

data _∈_ where
  sender : ∀{r≢q} -> r ∈ msgSingle r q r≢q l ∞gSub
  receiver : ∀{q≢r} -> r ∈ msgSingle q r q≢r l ∞gSub
  there : r ∞∈ ∞gSub -> r ∈ msgSingle p q p≢q l ∞gSub

data _∞∈_ where
  unbox : r ∈ force ∞g -> r ∞∈ ∞g

_∈?_ : (r : Fin n) -> (g : Global n) -> Dec (r ∈ g)
_∞∈?_ : (r : Fin n) -> (∞g : ∞Global n) -> Dec (r ∞∈ ∞g)

r ∈? endG = no (λ ())
r ∈? msgSingle p q p≢q l ∞gSub
  with  p ≟ r  | q ≟ r
... | yes refl | no _     = yes sender
... | no _     | yes refl = yes receiver
... | no _     | no _     with r ∞∈? ∞gSub
...                       | yes r∞∈∞gSub = yes (there r∞∈∞gSub)
...                       | no r∞∉∞gSub = no {!   !}
r ∈? msgSingle p q p≢q l ∞gSub
  with  p ≟ r  | q ≟ r
... | yes refl | yes refl = ⊥-elim (p≢q refl)

_∞∈?_ r g with r ∈? force g
... | yes r∈g = yes (unbox r∈g)
... | no  r∉g = no {!   !}

-- size-g : ∀ { n : ℕ } -> (g : Global n) -> ℕ
-- size-g endG = 0
-- size-g (msgSingle _ _ _ _ gSub) = suc (size-g gSub)

-- size-g-reduces :
--   ∀ { p≢q }
--   -> g ≡ msgSingle {n} p q p≢q l gSub
--   -> size-g g ≡ suc (size-g gSub)
-- size-g-reduces {g = endG} ()
-- size-g-reduces {g = msgSingle _ _ _ _ gSub} refl = refl

msgSingle-subst-left :
  ∀ { p≢q }
  -> g ≡ msgSingle {n} p q p≢q l (box gSub)
  -> (p≡p′ : p ≡ p′)
  -> g ≡ msgSingle {n} p′ q (≢-subst-left p≢q p≡p′) l (box gSub)
msgSingle-subst-left refl refl = refl

msgSingle-subst-right :
  ∀ { p≢q }
  -> g ≡ msgSingle {n} p q p≢q l (box gSub)
  -> (q≡q′ : q ≡ q′)
  -> g ≡ msgSingle {n} p q′ (≢-subst-right p≢q q≡q′) l (box gSub)
msgSingle-subst-right refl refl = refl

msgSingle-injective :
  ∀ { p≢q p′≢q′ }
  -> msgSingle {n} p q p≢q l (box gSub) ≡ msgSingle p′ q′ p′≢q′ l′ (box gSub′)
  -> p ≡ p′ × q ≡ q′ × l ≡ l′ × gSub ≡ gSub′
msgSingle-injective refl = refl , refl , refl , refl

data _-_→g_ {n : ℕ} : Global n -> Action n -> Global n -> Set where
  →g-prefix :
    ∀ { p≢q p≢q′ }
    -> msgSingle p q p≢q l (box gSub) - (action p q p≢q′ l) →g gSub
  →g-cont :
    ∀ { p≢q r≢s }
    -> gSub - (action p q p≢q l) →g gSub′
    -> p ≢ r
    -> q ≢ r
    -> p ≢ s
    -> q ≢ s
    -> msgSingle r s r≢s l′ (box gSub) - (action p q p≢q l) →g (msgSingle r s r≢s l′ (box gSub′))
