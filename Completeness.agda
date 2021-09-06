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
        lpReduce@(→l-send {lp' = lp'} .p refl _) lqReduce@(→l-recv {lp' = lq'} .q refl _)
    )
    with proj-inv-send {g = g} (trans (sym (_↔_.isProj assoc p)) (sym lp≡c[p]))
       | proj-inv-recv {g = g} (trans (sym (_↔_.isProj assoc q)) (sym lq≡c[q]))
...    | inj₁ (p≠q₁ , g'₁ , g-inv₁ , g'₁-proj-p)
       | inj₁ (_    , g'₂ , g-inv₂ , g'₂-proj-q)
        = g'₁ , (gReduce , record { isProj = isProj-g' })
    where
        injective = msgSingle-injective (trans (sym g-inv₁) g-inv₂)
        g'₁≡g'₂ : g'₁ ≡ g'₂
        g'₁≡g'₂ = proj₂ (proj₂ (proj₂ injective))
        gReduce : g - act →g g'₁
        gReduce with injective
        ... | refl , refl , refl , refl rewrite g-inv₁ = →g-prefix {n} {p} {q} {l} {g'₁} {p≠q₁} {p≠q}
        isProj-g' : (r : Fin n) -> lookup c' r ≡ project g'₁ r
        isProj-g' r with r ≟ p   | r ≟ q
        ...    | yes r≡p | yes r≡q = ⊥-elim (p≠q (trans (sym r≡p) r≡q))
        ...    | no r≠p  | yes r≡q rewrite r≡q
                                   rewrite c→c'
                                   rewrite lookup∘update q (c [ p ]≔ lp') lq'
                                   rewrite sym (g'₂-proj-q)
                                   rewrite sym (g'₁≡g'₂) = refl
        ...    | yes r≡p | no r≠q  rewrite r≡p
                                   rewrite c→c'
                                   rewrite lookup∘update′ p≠q (c [ p ]≔ lp') lq'
                                   rewrite lookup∘update p c lp'
                                   rewrite sym (g'₁-proj-p) = refl
        ...    | no r≠p  | no r≠q  rewrite c→c'
                                   rewrite lookup∘update′ r≠q (c [ p ]≔ lp') lq'
                                   rewrite lookup∘update′ r≠p c lp'
                                   rewrite (sym (proj-prefix-other p q r {p≠q₁} {l} g'₁ (¬≡-flip r≠p) (¬≡-flip r≠q)))
                                   rewrite _↔_.isProj assoc r
                                   rewrite g-inv₁ = refl

...    | inj₁ (_ , _ , g-inv₁ , _)
       | inj₂ (_ , s , _ , _ , _ , g-inv₂ , _ , s≠q , _)
        = ⊥-elim (s≠q (sym (proj₁ (proj₂ injective))))
    where
        injective = msgSingle-injective (trans (sym g-inv₁) g-inv₂)

...    | inj₂ (r , _ , _ , _ , _ , g-inv₁ , r≠p , _ , _)
       | inj₁ (_ , _ , g-inv₂ , _)
        = ⊥-elim (r≠p (proj₁ injective))
    where
        injective = msgSingle-injective (trans (sym g-inv₁) g-inv₂)

...    | inj₂ (r₁ , s₁ , r≠s , l'₁ , g'₁ , g-inv₁ , r≠p  , s≠p  , g'₁-proj-p)
       | inj₂ (r₂ , s₂ , _   , l'₂ , g'₂ , g-inv₂ , r≠q' , s≠q' , g'₂-proj-q)
        = g' , ({! gReduce  !} , record { isProj = isProj-g' })
    where
        injective = msgSingle-injective (trans (sym g-inv₁) g-inv₂)
        g'₁≡g'₂ : g'₁ ≡ g'₂
        g'₁≡g'₂ = proj₂ (proj₂ (proj₂ injective))
        r₁≡r₂ : r₁ ≡ r₂
        r₁≡r₂ = proj₁ injective
        s₁≡s₂ : s₁ ≡ s₂
        s₁≡s₂ = proj₁ (proj₂ injective)
        r≠q : r₁ ≢ q
        r≠q = ≢-subst-left r≠q' (sym r₁≡r₂)
        s≠q : s₁ ≢ q
        s≠q = ≢-subst-left s≠q' (sym s₁≡s₂)
        lr' = project g'₁ r₁
        ls' = project g'₁ s₁
        cSub : Configuration n
        cSub = (c [ r₁ ]≔ lr') [ s₁ ]≔ ls'
        cSub' : Configuration n
        cSub' = (cSub [ p ]≔ lp') [ q ]≔ lq'
        cSub[p]-lookup : sendSingle q l lp' ≡ lookup cSub p
        cSub[p]-lookup rewrite lp≡c[p]
                       rewrite sym (lookup∘update′ (¬≡-flip r≠p) c lr')
                       rewrite sym (lookup∘update′ (¬≡-flip s≠p) (c [ r₁ ]≔ lr') ls') = refl
        cSub[q]-lookup : recvSingle p l lq' ≡ lookup cSub q
        cSub[q]-lookup rewrite lq≡c[q]
                       rewrite sym (lookup∘update′ (¬≡-flip r≠q) c lr')
                       rewrite sym (lookup∘update′ (¬≡-flip s≠q) (c [ r₁ ]≔ lr') ls') = refl
        isProj-g'₁ : (t : Fin n) -> lookup cSub t ≡ project g'₁ t
        isProj-g'₁ t
            with r₁ ≟ t   | s₁ ≟ t
        ...    | yes r≡t  | no s≠t  rewrite sym r≡t
                                    rewrite lookup∘update′ (¬≡-flip s≠t) (c [ r₁ ]≔ lr') ls'
                                    rewrite lookup∘update r₁ c lr' = refl
        ...    | no _     | yes s≡t rewrite sym s≡t
                                    rewrite lookup∘update s₁ (c [ r₁ ]≔ lr') ls' = refl
        ...    | no r≠t   | no s≠t  rewrite lookup∘update′ (¬≡-flip s≠t) (c [ r₁ ]≔ lr') ls'
                                    rewrite lookup∘update′ (¬≡-flip r≠t) c lr'
                                    rewrite sym (proj-prefix-other r₁ s₁ t {r≠s} {l'₁} g'₁ r≠t s≠t)
                                    rewrite _↔_.isProj assoc t
                                    rewrite g-inv₁ = refl
        ...    | yes r≡t  | yes s≡t = ⊥-elim (r≠s (trans r≡t (sym s≡t)))
        cSub→cSub' : cSub - act →c cSub'
        cSub→cSub' = →c-comm cSub p≠q cSub[p]-lookup cSub[q]-lookup refl lpReduce lqReduce
        assocSub : g'₁ ↔ cSub
        assocSub = record { isProj = isProj-g'₁ }
        ∃g'' : ∃[ g'' ] ((g'₁ - act →g g'') × (g'' ↔ cSub'))
        ∃g'' = completeness assocSub cSub→cSub'
        g'' = proj₁ ∃g''
        g'Reduce : g'₁ - act →g g''
        g'Reduce = proj₁ (proj₂ ∃g'')
        g''Assoc : g'' ↔ cSub'
        g''Assoc = proj₂ (proj₂ ∃g'')
        g' = msgSingle r₁ s₁ r≠s l'₁ g''
        proj-g'₁-g''-eq : (t : Fin n) -> t ≢ p -> t ≢ q -> project g'₁ t ≡ project g'' t
        proj-g'₁-g''-eq t t≠p t≠q with t ≟ p   | t ≟ q
        ...                          | no _    | no _    rewrite sym (_↔_.isProj assocSub t)
                                                         rewrite sym (lookup∘update′ t≠p cSub lp')
                                                         rewrite sym (lookup∘update′ t≠q (cSub [ p ]≔ lp') lq')
                                                         rewrite _↔_.isProj g''Assoc t = refl
        ...                          | yes t≡p | _       = ⊥-elim (t≠p t≡p)
        ...                          | _       | yes t≡q = ⊥-elim (t≠q t≡q)
        gReduce : (msgSingle r₁ s₁ r≠s l'₁ g'₁) - act →g (msgSingle r₁ s₁ r≠s l'₁ g'')
        gReduce = →g-cont {l' = l'₁} {r≠s = r≠s} g'Reduce (¬≡-flip r≠p) (¬≡-flip r≠q) (¬≡-flip s≠p) (¬≡-flip s≠q)
        isProj-g' : (t : Fin n) -> lookup c' t ≡ project g' t
        isProj-g' t
            with r₁ ≟ t   | s₁ ≟ t
        ...    | yes r≡t  | no _    rewrite sym r≡t
                                    rewrite c→c'
                                    rewrite lookup∘update′ r≠q (c [ p ]≔ lp') lq'
                                    rewrite lookup∘update′ r≠p c lp'
                                    rewrite _↔_.isProj assoc r₁
                                    rewrite g-inv₁
                                    rewrite proj-prefix-send r₁ s₁ {l'₁} g'₁ r≠s
                                    rewrite cong (λ lt -> sendSingle s₁ l'₁ lt) (sym (_↔_.isProj assocSub r₁))
                                    rewrite cong (λ lt -> sendSingle s₁ l'₁ lt) (sym (lookup∘update′ r≠p cSub lp'))
                                    rewrite cong (λ lt -> sendSingle s₁ l'₁ lt) (sym (lookup∘update′ r≠q (cSub [ p ]≔ lp') lq'))
                                    = cong (λ lt → sendSingle s₁ l'₁ lt) ({! trans   !} )
        ...    | no _     | yes s≡t = {!   !}
        ...    | no r≠t   | no s≠t  = {!   !}
        ...    | yes r≡t  | yes s≡t = ⊥-elim (r≠s (trans r≡t (sym s≡t)))
