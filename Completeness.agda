open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

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
completeness assoc (→c-comm {p} {q} {l} c p≠q lp≡c[p] lq≡c[q] c→c' (→l-send .p .p≠q) (→l-recv .q .p≠q)) = ?
