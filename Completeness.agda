open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (suc; zero)
open import Data.Nat.Properties using (suc-injective; 0≢1+n)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (lookup; _[_]≔_)
open import Data.Vec.Properties using (lookup∘update; lookup∘update′)
open import Relation.Binary.PropositionalEquality using (refl; sym; cong; trans; _≡_; _≢_; module ≡-Reasoning)
open import Relation.Nullary using (yes; no)
open ≡-Reasoning

open import Common
open import Global
open import Local
open import Projection

completeness :
  ∀{ n } { act : Action n } { c c′ g g-size }
  -> { g-size-is-size-g : g-size ≡ size-g g }
  -> g ↔ c
  -> c - act →c c′
  -> ∃[ g′ ] g - act →g g′ × g′ ↔ c′
completeness assoc (→c-comm c p≢q lp≡c[p] lq≡c[q] c→c′ (→l-send p _ _) (→l-send .p _ _))
  = ⊥-elim (p≢q refl)
completeness assoc (→c-comm c p≢q lp≡c[p] lq≡c[q] c→c′ (→l-recv p _ _) (→l-send .p _ _))
  = ⊥-elim (p≢q refl)
completeness assoc (→c-comm c p≢q lp≡c[p] lq≡c[q] c→c′ (→l-recv p _ _) (→l-recv .p _ _))
  = ⊥-elim (p≢q refl)
completeness
  {n}
  {act}
  {c′ = c′}
  {g = g}
  {g-size = g-size}
  {g-size-is-size-g = g-size-is-size-g}
  assoc
  (→c-comm {p} {q} {l} c p≢q lp≡c[p] lq≡c[q] refl
    lpReduce@(→l-send {lp = lp} {lpSub = lp′} .p refl p≢q-p) lqReduce@(→l-recv {lp = lq} {lpSub = lq′} .q refl p≢q-q)
  )
  with proj-inv-send-recv {g = g} (trans (sym (_↔_.isProj assoc p)) (sym lp≡c[p])) (trans (sym (_↔_.isProj assoc q)) (sym lq≡c[q]))
... | inj₁ (p≢q , g′ , refl , refl , refl)
    = g′ , →g-prefix , record { isProj = isProj-g′ }
    where
      isProj-g′ : (r : Fin n) -> lookup c′ r ≡ project g′ r
      isProj-g′ r with r ≟ p | r ≟ q
      ...   | yes refl | yes refl = ⊥-elim (p≢q refl)
      ...   | no r≢p   | yes refl
        rewrite lookup∘update q (c [ p ]≔ lp′) lq′
        = refl
      ...   | yes refl | no r≢q
        rewrite lookup∘update′ p≢q (c [ p ]≔ lp′) lq′
        rewrite lookup∘update p c lp′
        = refl
      ...    | no r≢p  | no r≢q
        rewrite lookup∘update′ r≢q (c [ p ]≔ lp′) lq′
        rewrite lookup∘update′ r≢p c lp′
        rewrite sym (proj-prefix-other {l = l} p q r {p≢q} g′ (¬≡-flip r≢p) (¬≡-flip r≢q))
        rewrite _↔_.isProj assoc r
        = refl
... | inj₂ (r , s , r≢s , l′ , gSub , refl , r≢p , s≢p , r≢q , s≢q , gSub-proj-p , gSub-proj-q)
    with g-size
...   | zero
      = ⊥-elim (0≢1+n g-size-is-size-g)
...   | suc gSub-size
      = g′ , gReduce , record { isProj = isProj-g′ }
        where
          lrSub = project gSub r
          lsSub = project gSub s
          remove-prefix-g : ∃[ cSub ] cSub ≡ (c [ r ]≔ lrSub) [ s ]≔ lsSub × gSub ↔ cSub
          remove-prefix-g = config-gt-remove-prefix g c assoc refl
          completeness-gSub : ∃[ gSub′ ] gSub - act →g gSub′ × gSub′ ↔ ((((c [ r ]≔ lrSub) [ s ]≔ lsSub) [ p ]≔ lp′) [ q ]≔ lq′)
          completeness-gSub with remove-prefix-g
          ... | cSub , refl , gSub↔cSub = completeness {g = gSub} {g-size = gSub-size} {gSub-size-is-size-gSub} gSub↔cSub cSub→cSub′
            where
              gSub-size-is-size-gSub : gSub-size ≡ size-g gSub
              gSub-size-is-size-gSub = suc-injective g-size-is-size-g
              cSub′ = (cSub [ p ]≔ lp′) [ q ]≔ lq′
              cSub→cSub′ : cSub - act →c cSub′
              cSub→cSub′
                with remove-prefix-g
              ... | cSub , refl , gSub↔cSub = →c-comm cSub p≢q lp≡cSub[p] lq≡cSub[q] refl lpReduce lqReduce
                where
                  lp≡cSub[p] : lp ≡ lookup cSub p
                  lp≡cSub[p]
                    rewrite lp≡c[p]
                    rewrite sym (lookup∘update′ (¬≡-flip r≢p) c lrSub)
                    rewrite sym (lookup∘update′ (¬≡-flip s≢p) (c [ r ]≔ lrSub) lsSub)
                    = refl
                  lq≡cSub[q] : lq ≡ lookup cSub q
                  lq≡cSub[q]
                    rewrite lq≡c[q]
                    rewrite sym (lookup∘update′ (¬≡-flip r≢q) c lrSub)
                    rewrite sym (lookup∘update′ (¬≡-flip s≢q) (c [ r ]≔ lrSub) lsSub)
                    = refl
          g′ : Global n
          g′ with completeness-gSub
          ... | gSub′ , _ , _ = msgSingle r s r≢s l′ gSub′
          gReduce : g - act →g g′
          gReduce with completeness-gSub
          ... | gSub′ , gSubReduce , gSub′↔cSub′
            = →g-cont gSubReduce (¬≡-flip r≢p) (¬≡-flip r≢q) (¬≡-flip s≢p) (¬≡-flip s≢q)
          isProj-g′ : (t : Fin n) -> lookup c′ t ≡ project g′ t
          isProj-g′ t with remove-prefix-g | completeness-gSub
          ... | cSub , un-c′ , g′↔c′ | gSub′ , gSubReduce , gSub′↔cSub′
              with r ≟ t  | s ≟ t
          ... | yes refl | yes refl = ⊥-elim (r≢s refl)
          ... | no r≢t   | yes refl
              rewrite sym (_↔_.isProj gSub′↔cSub′ s)
              rewrite lookup∘update′ s≢q (c [ p ]≔ lp′) lq′
              rewrite lookup∘update′ s≢p c lp′
              rewrite _↔_.isProj assoc s
              rewrite proj-prefix-recv {l = l′} r s gSub r≢s
              rewrite lookup∘update′ s≢q (((c [ r ]≔ lrSub) [ s ]≔ lsSub) [ p ]≔ lp′) lq′
              rewrite lookup∘update′ s≢p ((c [ r ]≔ lrSub) [ s ]≔ lsSub) lp′
              rewrite lookup∘update s (c [ r ]≔ lrSub) lsSub
              = refl
          ... | yes refl | no s≢t
              rewrite sym (_↔_.isProj gSub′↔cSub′ r)
              rewrite lookup∘update′ r≢q (c [ p ]≔ lp′) lq′
              rewrite lookup∘update′ r≢p c lp′
              rewrite _↔_.isProj assoc r
              rewrite proj-prefix-send {l = l′} r s gSub r≢s
              rewrite lookup∘update′ r≢q (((c [ r ]≔ lrSub) [ s ]≔ lsSub) [ p ]≔ lp′) lq′
              rewrite lookup∘update′ r≢p ((c [ r ]≔ lrSub) [ s ]≔ lsSub) lp′
              rewrite lookup∘update′ r≢s (c [ r ]≔ lrSub) lsSub
              rewrite lookup∘update r c lrSub
              = refl
          ... | no r≢t  | no s≢t
              rewrite proj-prefix-other {l = l′} r s t {r≢s} gSub′ r≢t s≢t
              with p ≟ t  | q ≟ t
          ...   | yes refl | yes refl = ⊥-elim (p≢q refl)
          ...   | yes refl | no  q≢t
                  rewrite lookup∘update′ p≢q (c [ p ]≔ lp′) lq′
                  rewrite lookup∘update p c lp′
                  rewrite sym (_↔_.isProj gSub′↔cSub′ p)
                  rewrite lookup∘update′ p≢q (((c [ r ]≔ lrSub) [ s ]≔ lsSub) [ p ]≔ lp′) lq′
                  rewrite lookup∘update p ((c [ r ]≔ lrSub) [ s ]≔ lsSub) lp′
                  = refl
          ...   | no  p≢t  | yes refl
                  rewrite lookup∘update q (c [ p ]≔ lp′) lq′
                  rewrite sym (_↔_.isProj gSub′↔cSub′ q)
                  rewrite lookup∘update q (((c [ r ]≔ lrSub) [ s ]≔ lsSub) [ p ]≔ lp′) lq′
                  = refl
          ...   | no  p≢t  | no  q≢t
                  rewrite lookup∘update′ (¬≡-flip q≢t) (c [ p ]≔ lp′) lq′
                  rewrite lookup∘update′ (¬≡-flip p≢t) c lp′
                  rewrite sym (_↔_.isProj gSub′↔cSub′ t)
                  rewrite lookup∘update′ (¬≡-flip q≢t) (((c [ r ]≔ lrSub) [ s ]≔ lsSub) [ p ]≔ lp′) lq′
                  rewrite lookup∘update′ (¬≡-flip p≢t) ((c [ r ]≔ lrSub) [ s ]≔ lsSub) lp′
                  rewrite lookup∘update′ (¬≡-flip s≢t) (c [ r ]≔ lrSub) lsSub
                  rewrite lookup∘update′ (¬≡-flip r≢t) c lrSub
                  = refl
