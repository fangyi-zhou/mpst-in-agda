open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl; sym; trans; _≡_)

open import Common
open import Global
open import Local
open import Projection

completeness :
    ∀{ n } { act : Action n } { c c' g }
    -> g ↔ c
    -> c - act →c c'
    -> ∃[ g' ] ((g - act →g g') × (g' ↔ c'))
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-send p .p≠q) (→l-send .p .p≠q)) = ⊥-elim (p≠q refl)
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-recv p .p≠q) (→l-send .p .p≠q)) = ⊥-elim (p≠q refl)
completeness assoc (→c-comm c p≠q lp≡c[p] lq≡c[q] c→c' (→l-recv p .p≠q) (→l-recv .p .p≠q)) = ⊥-elim (p≠q refl)
completeness {n} {act} {g = g} assoc (→c-comm {p} {q} {l} c p≠q lp≡c[p] lq≡c[q] c→c' (→l-send .p .p≠q) (→l-recv .q .p≠q))
    with proj-inv-send {g = g} (trans (sym (_↔_.isProj assoc p)) (sym lp≡c[p])) | proj-inv-recv {g = g} (trans (sym (_↔_.isProj assoc q)) (sym lq≡c[q]))
...  | inj₁ (p≠q₁ , g'₁ , g₁ , g'₁-proj-p) | inj₁ (p≠q₂ , g'₂ , g₂ , g'₂-proj-q) = g'₁ , ({! gReduce    !} , {!   !})
    where
        lhs≡rhs : msgSingle p q p≠q₁ l g'₁ ≡ msgSingle p q p≠q₂ l g'₂
        lhs≡rhs = trans (sym g₁) g₂
        injective = msgSingle-injective lhs≡rhs
        g'₁≡g'₂ : g'₁ ≡ g'₂
        g'₁≡g'₂ = proj₂ (proj₂ (proj₂ injective))
        gReduce : g - act →g g'₁
        gReduce rewrite g₁ = {!  →g-prefix {n} {p} {q} {l} {g'₁} {p≠q₁} !}
...  | inj₁ x | inj₂ y = {!   !}
...  | inj₂ y | inj₁ x = {!   !}
...  | inj₂ y | inj₂ y₁ = {!   !}
