open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)

open import Common

data Global (n : ℕ) (ℓ : ℕ) : Set where
  endG : Global n ℓ
  msgSingle : (p q : Fin n) -> p ≢ q -> Fin ℓ -> Global n ℓ -> Global n ℓ

private
  variable
    n ℓ : ℕ
    p p′ q q′ r s : Fin n
    l l′ : Fin ℓ
    g gSub gSub′ : Global n ℓ

infix 4 _-_→g_

msgSingle′ : (p q : Fin n) -> {False (p ≟ q)} -> Fin ℓ -> Global n ℓ -> Global n ℓ
msgSingle′ p q {p≢q} l gSub = msgSingle p q (toWitnessFalse p≢q) l gSub

size-g : ∀ { n : ℕ } -> (g : Global n ℓ) -> ℕ
size-g endG = 0
size-g (msgSingle _ _ _ _ gSub) = suc (size-g gSub)

size-g-reduces :
  ∀ { p≢q }
  -> g ≡ msgSingle {n} p q p≢q l gSub
  -> size-g g ≡ suc (size-g gSub)
size-g-reduces {g = endG} ()
size-g-reduces {g = msgSingle _ _ _ _ gSub} refl = refl

msgSingle-subst-left :
  ∀ { p≢q }
  -> g ≡ msgSingle {n} p q p≢q l gSub
  -> (p≡p′ : p ≡ p′)
  -> g ≡ msgSingle {n} p′ q (≢-subst-left p≢q p≡p′) l gSub
msgSingle-subst-left refl refl = refl

msgSingle-subst-right :
  ∀ { p≢q }
  -> g ≡ msgSingle {n} p q p≢q l gSub
  -> (q≡q′ : q ≡ q′)
  -> g ≡ msgSingle {n} p q′ (≢-subst-right p≢q q≡q′) l gSub
msgSingle-subst-right refl refl = refl

msgSingle-injective :
  ∀ { p≢q p′≢q′ }
  -> msgSingle {n} p q p≢q l gSub ≡ msgSingle p′ q′ p′≢q′ l′ gSub′
  -> p ≡ p′ × q ≡ q′ × l ≡ l′ × gSub ≡ gSub′
msgSingle-injective refl = refl , refl , refl , refl

data _-_→g_ {n : ℕ} : Global n ℓ -> Action n ℓ -> Global n ℓ -> Set where
  →g-prefix :
    ∀ { p≢q p≢q′ }
    -> (msgSingle p q p≢q l gSub) - (action p q p≢q′ l) →g gSub
  →g-cont :
    ∀ { p≢q r≢s }
    -> gSub - (action p q p≢q l) →g gSub′
    -> p ≢ r
    -> q ≢ r
    -> p ≢ s
    -> q ≢ s
    -> (msgSingle r s r≢s l′ gSub) - (action p q p≢q l) →g (msgSingle r s r≢s l′ gSub′)
