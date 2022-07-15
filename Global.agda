{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_; suc; inject₁; fromℕ; toℕ; lower₁; _<_; zero)
open import Data.Fin.Properties using (suc-injective; toℕ-injective; toℕ-fromℕ; toℕ-lower₁; toℕ-inject₁)
open import Data.Nat using (ℕ; suc; zero; s≤s; z≤n; _≤_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; ≤⇒≤′)
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
    guardedVarG : ∀{target} {x : Fin t} -> target Data.Fin.< x -> GuardedG target (varG x)
    {-- If we remove muG, then we remove duplicate recursion -}
    guardedRecG : ∀{target g guarded} -> GuardedG (suc target) g -> GuardedG target (recG g guarded)

private
  variable
    n : ℕ
    t t′ : ℕ
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
incr-Guarded (guardedRecG x) = guardedRecG (incr-Guarded x)

guarded-weaken : ∀{target target′} -> target′ Data.Fin.≤ target -> GuardedG target g -> GuardedG target′ g
guarded-weaken target′≤target endGlobal = endGlobal
guarded-weaken target′≤target msg = msg
guarded-weaken target′≤target (guardedVarG target<x) = guardedVarG (≤-trans (s≤s target′≤target) target<x)
guarded-weaken {target = target} {target′ = target′} target′≤target (guardedRecG guarded)
  = guardedRecG (guarded-weaken (s≤s target′≤target) guarded)

inject₁-G : Global n t -> Global n (suc t)
inject₁-guarded : ∀{target} -> GuardedG target g -> GuardedG (inject₁ target) (inject₁-G g)

inject₁-G endG = endG
inject₁-G (msgSingle p q p≢q l g) = msgSingle p q p≢q l (inject₁-G g)
inject₁-G (varG recVar) = varG (inject₁ recVar)
inject₁-G (recG g x) = recG (inject₁-G g) {!   x!}

inject₁-guarded endGlobal = endGlobal
inject₁-guarded msg = msg
inject₁-guarded {target = target} (guardedVarG {x = x} target<x)
  = guardedVarG (≤-trans (≤-trans (≤-reflexive (cong suc (toℕ-inject₁ target))) target<x) (≤-reflexive (sym (toℕ-inject₁ x))))
inject₁-guarded (guardedRecG x) = guardedRecG (inject₁-guarded x)

inject-G : t ≤ t′ -> Global n t -> Global n t′
inject′-G : t ≤′ t′ -> Global n t -> Global n t′
inject-G t≤t′ g = inject′-G (≤⇒≤′ t≤t′) g
inject′-G ≤′-refl g = g
inject′-G (≤′-step t≤t′) g = inject₁-G (inject′-G t≤t′ g)


-- Inspired by Thiemann
_[_↦_] : Global n (suc t) -> Fin (suc t) -> Global n 0 -> Global n t
-- _guarded[_] : ∀{t : ℕ} {g : Global n (suc t)} {g′ : Global n 0} {target} -> GuardedG (inject₁ target) g -> GuardedG target g′ -> GuardedG target (g [ g′ ])

endG [ idx ↦ g′ ] = endG
msgSingle p q p≢q l g [ idx ↦ g′ ] = msgSingle p q p≢q l (g [ idx ↦ g′ ])
recG g x [ idx ↦ g′ ] = recG (g [ suc idx ↦ g′ ]) {!   !}
_[_↦_] {t = t} (varG zero) zero g′ = inject-G z≤n g′
_[_↦_] {t = suc t} (varG zero) (suc idx) g′ = varG {t = suc t} zero
_[_↦_] (varG (suc recVar)) zero g′ = varG recVar
_[_↦_] {t = suc t} (varG (suc recVar)) (suc idx) g′ = inject₁-G (varG recVar [ idx ↦ g′ ])


{-
endGlobal guarded[ guardedG′ ] = endGlobal
msg guarded[ guardedG′ ] = msg
_guarded[_] {t = t} {target = target} (guardedVarG {x = x} inject₁-target<x) guardedG′ with t Data.Nat.≟ toℕ x
... | yes _ = guardedG′
... | no notMax = guardedVarG target<x
    where
      target<x : target < lower₁ x notMax
      target<x rewrite toℕ-lower₁ x notMax rewrite (sym (toℕ-inject₁ target))= inject₁-target<x
guardedRecG guardedG guarded[ guardedG′ ] = guardedRecG (guardedG guarded[ incr-Guarded guardedG′ ])
-}

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
