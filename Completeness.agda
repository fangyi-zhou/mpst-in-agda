open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Common using (Action; action)
open import Global using (_-_→g_)
open import Local using (_-_→c_; →c-comm; →l-send; →l-recv)
open import Projection using (_↔_)

completeness :
    ∀{ n } { act : Action n } { c c' g }
    -> g ↔ c
    -> c - act →c c'
    -> ∃[ g' ] ((g - act →g g') × (g' ↔ c'))
completeness {n} {act = action .p .p .p≠q .l} {c} assoc (→c-comm {p} {.p} {l} .c p≠q lp≡c[p] lq≡c[q] c→c' (→l-send .p .p≠q) (→l-send .p .p≠q)) = ⊥-elim (p≠q refl)
completeness {n} {act = action .p .q .p≠q .l} {c} assoc (→c-comm {p} {q} {l} .c p≠q lp≡c[p] lq≡c[q] c→c' (→l-send .p .p≠q) (→l-recv .q .p≠q)) = ?
completeness {n} {act = action .p .p .p≠q .l} {c} assoc (→c-comm {p} {.p} {l} .c p≠q lp≡c[p] lq≡c[q] c→c' (→l-recv .p .p≠q) (→l-send .p .p≠q)) = ⊥-elim (p≠q refl)
completeness {n} {act = action .p .p .p≠q .l} {c} assoc (→c-comm {p} {.p} {l} .c p≠q lp≡c[p] lq≡c[q] c→c' (→l-recv .p .p≠q) (→l-recv .p .p≠q)) = ⊥-elim (p≠q refl)
