open import Data.Product using (∃-syntax; _×_)

open import Common using (Action)
open import Global using (_-_→g_)
open import Local using (_-_→c_)
open import Projection using (_↔_)

completeness :
    ∀{ n } { act : Action n } { c c' g }
    -> g ↔ c
    -> c - act →c c'
    -> ∃[ g' ] ((g - act →g g') × (g' ↔ c'))
completeness assoc cReduce
    = ?
