open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)

open import Common

data Global (n : ℕ) : Set where
    endG : Global n
    msgSingle : (p q : Fin n) -> ¬ (p ≡ q) -> Label -> Global n -> Global n

msgSingle-subst-left :
    ∀ { n : ℕ } { p q p≠q l g' p' g }
    -> g ≡ msgSingle {n} p q p≠q l g'
    -> (p≡p' : p ≡ p')
    -> g ≡ msgSingle {n} p' q (≢-subst-left p≠q p≡p') l g'
msgSingle-subst-left refl refl = refl

msgSingle-subst-right :
    ∀ { n : ℕ } { p q p≠q l g' q' g }
    -> g ≡ msgSingle {n} p q p≠q l g'
    -> (q≡q' : q ≡ q')
    -> g ≡ msgSingle {n} p q' (≢-subst-right p≠q q≡q') l g'
msgSingle-subst-right refl refl = refl

msgSingle-injective :
    ∀ { n : ℕ } { p q p≠q l g' p' q' p'≠q' l' g'' }
    -> msgSingle {n} p q p≠q l g' ≡ msgSingle p' q' p'≠q' l' g''
    -> p ≡ p' × q ≡ q' × l ≡ l' × g' ≡ g''
msgSingle-injective refl = refl , (refl , (refl , refl))

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
