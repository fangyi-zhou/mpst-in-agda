open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (lookup; _[_]≔_)
open import Data.Vec.Properties using (lookup∘update; lookup∘update′)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; _≡_)
open import Relation.Nullary using (yes; no)

open import Common
open import Global
open import Local
open import Projection

completeness :
    ∀{ n } { act : Action n } { c c' g }
    -> g ↔ c
    -> c - act →c c'
    -> ∃[ g' ] ((g - act →g g') × (g' ↔ c'))
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-send p _) (→l-send .p _))
    = ⊥-elim (p≠q refl)
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-recv p _) (→l-send .p _))
    = ⊥-elim (p≠q refl)
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-recv p _) (→l-recv .p _))
    = ⊥-elim (p≠q refl)
completeness
    {n}
    {act}
    {c' = c'}
    {g = g}
    assoc
    (→c-comm {p} {q} {l} c p≠q lp≡c[p] lq≡c[q] c→c'
        (→l-send {lt' = lp'} .p _) (→l-recv {lt' = lq'} .q _)
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

...    | inj₂ (r₁ , s₁ , r≠s , l'₁ , g'₁ , g-inv₁ , _ , _ , _)
       | inj₂ (r₂ , s₂ , _   , l'₂ , g'₂ , g-inv₂ , _ , _ , _)
        = g'₁ , (gReduce , record { isProj = isProj-g' })
    where
        injective = msgSingle-injective (trans (sym g-inv₁) g-inv₂)
        g'₁≡g'₂ : g'₁ ≡ g'₂
        g'₁≡g'₂ = proj₂ (proj₂ (proj₂ injective))
        postulate gReduce : g - act →g g'₁
        postulate isProj-g' : (r : Fin n) -> lookup c' r ≡ project g'₁ r
