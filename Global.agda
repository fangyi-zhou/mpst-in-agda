open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Data.Fin using (Fin; _≟_; suc; inject₁; fromℕ; toℕ)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_)

open import Common

{- n sets the number of participants, t is the deBruijn index of recursive variable -}
interleaved mutual
  data Global (n : ℕ) (t : ℕ) : Set
  unRec : ∀ {n t} -> Global n t -> ∃[ t′ ] Global n t′
  data Guarded {n t} : (target : Fin t) -> Global n t -> Set

  data Global n t where
    endG : Global n t
    msgSingle : (p q : Fin n) -> p ≢ q -> Label -> Global n t -> Global n t
    muG : (g : Global n (suc t)) -> Guarded (fromℕ t) g -> Global n t
    recG : (recVar : Fin t) -> Global n t
  unRec (muG g _) = unRec g
  unRec {t = t} g = t , g

  data Guarded target g where
    endG : ∀{target} -> Guarded target endG
    msgSingle : ∀{p q p≢q l gSub target} -> Guarded target (msgSingle p q p≢q l gSub)
    recG : ∀{target} {x : Fin t} -> target ≢ x -> Guarded target (recG x)
    {-- If we remove muG, then we remove duplicate recursion -}
    muG : ∀{target g guarded} -> Guarded target (muG g guarded)

private
  variable
    n : ℕ
    t : ℕ
    p p′ q q′ r s : Fin n
    p≢q : p ≢ q
    l l′ : Label
    g gSub gSub′ : Global n t

msgSingle′ : (p q : Fin n) -> {False (p ≟ q)} -> Label -> Global n t -> Global n t
msgSingle′ p q {p≢q} l gSub = msgSingle p q (toWitnessFalse p≢q) l gSub

{-
data ProductiveG {n : ℕ} {t : ℕ} (target : Fin t) : (g : Global n t) -> Set where
  end : ProductiveG target endG
  msg : ProductiveG target (msgSingle p q p≢q l gSub)
  rec : ProductiveG {t = suc t} (inject₁ target) gSub -> ProductiveG target (muG gSub)
  var : (recVar : Fin t) -> recVar ≢ target -> ProductiveG target (recG recVar)

data GuardedG {n : ℕ} (t : ℕ) : (g : Global n t) -> Set where
  end : GuardedG t endG
  msg : GuardedG t gSub -> GuardedG t (msgSingle p q p≢q l gSub)
  rec : ProductiveG (fromℕ t) gSub -> GuardedG (suc t) gSub -> GuardedG t (muG gSub)
  var : (recVar : Fin t) -> GuardedG t (recG recVar)
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
