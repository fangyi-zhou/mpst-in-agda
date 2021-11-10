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
        lpReduce@(→l-send {lp' = lp'} .p refl p≠q-p) lqReduce@(→l-recv {lp' = lq'} .q refl p≠q-q)
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
... | inj₂ (r , s , r≠s , l' , g' , g-inv , r≠p  , s≠p , r≠q , s≠q , g'-proj-p ,  g'-proj-q) = {!   !}