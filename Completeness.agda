open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
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

{-# TERMINATING #-}
completeness :
    ∀{ n } { act : Action n } { c c' g }
    -> g ↔ c
    -> c - act →c c'
    -> ∃[ g' ] ((g - act →g g') × (g' ↔ c'))
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-send p _ _) (→l-send .p _ _))
    = ⊥-elim (p≠q refl)
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-recv p _ _) (→l-send .p _ _))
    = ⊥-elim (p≠q refl)
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-recv p _ _) (→l-recv .p _ _))
    = ⊥-elim (p≠q refl)
completeness
    {n}
    {act}
    {c' = c'}
    {g = g}
    assoc
    (→c-comm {p} {q} {l} c p≠q lp≡c[p] lq≡c[q] c→c'
        lpReduce@(→l-send {lp = lp} {lp' = lp'} .p refl p≠q-p) lqReduce@(→l-recv {lp = lq} {lp' = lq'} .q refl p≠q-q)
    )
    with proj-inv-send-recv {g = g} (trans (sym (_↔_.isProj assoc p)) (sym lp≡c[p])) (trans (sym (_↔_.isProj assoc q)) (sym lq≡c[q]))
... | inj₁ (p≠q , g' , g-inv , g'-proj-p , g'-proj-q)
        = g' , (gReduce , record { isProj = isProj-g' })
    where
        gReduce : g - act →g g'
        gReduce rewrite g-inv = →g-prefix
        isProj-g' : (r : Fin n) -> lookup c' r ≡ project g' r
        isProj-g' r with r ≟ p   | r ≟ q
        ...    | yes r≡p | yes r≡q = ⊥-elim (p≠q (trans (sym r≡p) r≡q))
        ...    | no r≠p  | yes r≡q rewrite r≡q
                                   rewrite c→c'
                                   rewrite lookup∘update q (c [ p ]≔ lp') lq'
                                   rewrite sym (g'-proj-q) = refl
        ...    | yes r≡p | no r≠q  rewrite r≡p
                                   rewrite c→c'
                                   rewrite lookup∘update′ p≠q (c [ p ]≔ lp') lq'
                                   rewrite lookup∘update p c lp'
                                   rewrite sym (g'-proj-p) = refl
        ...    | no r≠p  | no r≠q  rewrite c→c'
                                   rewrite lookup∘update′ r≠q (c [ p ]≔ lp') lq'
                                   rewrite lookup∘update′ r≠p c lp'
                                   rewrite (sym (proj-prefix-other p q r {p≠q} {l} g' (¬≡-flip r≠p) (¬≡-flip r≠q)))
                                   rewrite _↔_.isProj assoc r
                                   rewrite g-inv = refl
... | inj₂ (r , s , r≠s , l' , gSub , g-inv , r≠p  , s≠p , r≠q , s≠q , gSub-proj-p ,  g'-proj-q)
        = g' , (gReduce , record { isProj = isProj-g' })
        where
            remove-prefix-g : ∃[ cSub ] ((cSub ≡ ((c [ r ]≔ (project gSub r)) [ s ]≔ (project gSub s))) × (gSub ↔ cSub))
            remove-prefix-g = config-gt-remove-prefix g c assoc g-inv
            completeness-gSub : ∃[ gSub' ] ((gSub - act →g gSub') × (gSub' ↔ ((((c [ r ]≔ project gSub r) [ s ]≔ project gSub s) [ p ]≔ lp') [ q ]≔ lq')))
            completeness-gSub with remove-prefix-g
            ...      | cSub , refl , gSub↔cSub = completeness gSub↔cSub cSub→cSub'
                where
                    cSub' = (cSub [ p ]≔ lp') [ q ]≔ lq'
                    cSub→cSub' : cSub - act →c cSub'
                    cSub→cSub' with remove-prefix-g
                    ...      | cSub , refl , gSub↔cSub = →c-comm cSub p≠q cSub[p]≡lp cSub[q]≡lq refl lpReduce lqReduce
                        where
                            cSub[p]≡lp : lp ≡ lookup cSub p
                            cSub[p]≡lp rewrite lp≡c[p]
                                    rewrite proj₁ (proj₂ remove-prefix-g)
                                    rewrite sym (lookup∘update′ (¬≡-flip r≠p) c (project gSub r))
                                    rewrite sym (lookup∘update′ (¬≡-flip s≠p) (c [ r ]≔ (project gSub r)) (project gSub s))
                                    = refl
                            cSub[q]≡lq : lq ≡ lookup cSub q
                            cSub[q]≡lq rewrite lq≡c[q]
                                    rewrite proj₁ (proj₂ remove-prefix-g)
                                    rewrite sym (lookup∘update′ (¬≡-flip r≠q) c (project gSub r))
                                    rewrite sym (lookup∘update′ (¬≡-flip s≠q) (c [ r ]≔ (project gSub r)) (project gSub s))
                                    = refl
            gSub' = proj₁ completeness-gSub
            g' = msgSingle r s r≠s l' gSub'
            gReduce : g - act →g g'
            gReduce with completeness-gSub
            ... | gSub' , gSubReduce , gSub'↔cSub' rewrite g-inv
                = →g-cont gSubReduce (¬≡-flip r≠p) (¬≡-flip r≠q) (¬≡-flip s≠p) (¬≡-flip s≠q)
            isProj-g' : (t : Fin n) -> lookup c' t ≡ project g' t
            isProj-g' t with remove-prefix-g | completeness-gSub
            ...       | cSub , un-c' , g'↔c' | gSub' , gSubReduce , gSub'↔cSub'
                with r ≟ t | s ≟ t
            ...  | yes r≡t | yes s≡t = ⊥-elim (r≠s (trans r≡t (sym s≡t)))
            ...  | no r≠t  | yes s≡t rewrite s≡t
                                     rewrite proj-prefix-recv r t {l'} gSub' r≠t
                                     = {!   !}
            ...  | yes r≡t | no s≠t  rewrite proj-prefix-send t s {l'} gSub' (¬≡-flip s≠t)
                                     = {!   !}
            ...  | no r≠t  | no s≠t  rewrite proj-prefix-other r s t {r≠s} {l'} gSub' r≠t s≠t
                                     = {!   !}
