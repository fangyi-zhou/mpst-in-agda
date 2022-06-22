open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_; suc; inject₁; fromℕ; toℕ; lower₁; _<_)
open import Data.Fin.Properties using (suc-injective; toℕ-injective; toℕ-fromℕ; toℕ-lower₁; toℕ-inject₁)
open import Data.Nat using (ℕ; suc; zero; s≤s; _≤_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)

open import Common

{- n sets the number of participants, t is the deBruijn index of recursive variable -}
interleaved mutual
  data Global (n : ℕ) (t : ℕ) : Set
  data GuardedG {n t} : (target : Fin t) -> Global n t -> Set

  data Global n t where
    endG : Global n t
    msgSingle : (p q : Fin n) -> p ≢ q -> Label -> Global n t -> Global n t
    recG : (g : Global n (suc t)) -> GuardedG (fromℕ t) g -> Global n t
    varG : (recVar : Fin t) -> Global n t

  data GuardedG target g where
    endGlobal : ∀{target} -> GuardedG target endG
    msg : ∀{p q p≢q l gSub target} -> GuardedG target (msgSingle p q p≢q l gSub)
    guardedVarG : ∀{target} {x : Fin t} -> x < target -> GuardedG target (varG x)
    {-- If we remove muG, then we remove duplicate recursion -}
    guardedRecG : ∀{target g guarded} -> GuardedG target (recG g guarded)

private
  variable
    n : ℕ
    t : ℕ
    p p′ q q′ r s : Fin n
    p≢q : p ≢ q
    l l′ : Label
    g g′ gSub gSub′ : Global n t

msgSingle′ : (p q : Fin n) -> {False (p ≟ q)} -> Label -> Global n t -> Global n t
msgSingle′ p q {p≢q} l gSub = msgSingle p q (toWitnessFalse p≢q) l gSub

incr : Global n t -> Global n (suc t)
incr-Guarded : ∀{target} -> GuardedG target g -> GuardedG (suc target) (incr g)

incr endG = endG
incr (msgSingle p q p≢q l g) = msgSingle p q p≢q l (incr g)
incr (varG recVar) = varG (suc recVar)
incr (recG g guardedG) = recG (incr g) (incr-Guarded guardedG)

incr-Guarded endGlobal = endGlobal
incr-Guarded msg = msg
incr-Guarded (guardedVarG x) = guardedVarG (s≤s x)
incr-Guarded guardedRecG = guardedRecG

guarded-weaken : ∀{target target′} -> target Data.Fin.≤ target′ -> GuardedG target g -> GuardedG target′ g
guarded-weaken target≤target′ endGlobal = endGlobal
guarded-weaken target≤target′ msg = msg
guarded-weaken target≤target′ (guardedVarG x<target) = guardedVarG (≤-trans x<target target≤target′)
guarded-weaken target≤target′ guardedRecG = guardedRecG

_[_] : Global n (suc t) -> Global n t -> Global n t
_guarded[_] : ∀{t : ℕ} {g : Global n (suc t)} {g′ : Global n t} {target} -> GuardedG (inject₁ target) g -> GuardedG target g′ -> GuardedG target (g [ g′ ])

endG [ g′ ] = endG
msgSingle p q p≢q l g [ g′ ] = msgSingle p q p≢q l (g [ g′ ])
_[_] {t = t} (varG recVar) g′  with t Data.Nat.≟ toℕ recVar
... | yes _ = g′
... | no  notMax = varG (lower₁ recVar notMax)
_[_] {t = t} (recG g guardedG) g′ = recG (g [ incr g′ ]) ({! _guarded[_] {target = fromℕ t}  !})

endGlobal guarded[ guardedG′ ] = endGlobal
msg guarded[ guardedG′ ] = msg
_guarded[_] {t = t} {target = target} (guardedVarG {x = x} xx) guardedG′ with t Data.Nat.≟ toℕ x
... | yes _ = guardedG′
... | no xxx = guardedVarG x<target
    where
      x<target : suc (toℕ (lower₁ x xxx)) ≤ toℕ target
      x<target rewrite toℕ-lower₁ x xxx rewrite sym (toℕ-inject₁ target) = xx
guardedRecG guarded[ guardedG′ ] = guardedRecG

{-
size-g : ∀ { n : ℕ } -> (g : Global n t) -> ℕ
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
-}

{- Reduction is only defined over closed global types -}
data _-_→g_ {n : ℕ} : Global n zero -> Action n -> Global n zero -> Set where
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
