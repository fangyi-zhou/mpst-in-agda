open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Vec using (lookup)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_)

open import Common using (Label)
open import Global using (Global)
open import Local using (Local; Configuration)

project : ∀{ n : ℕ } -> Global n -> Fin n -> Local n
project Global.End r = Local.End
project (Global.MsgSingle p q p≠q l g) r with p ≟ r | q ≟ r
...                                     | yes _   | no _    = Local.Send q l (project g r)
...                                     | no _    | yes _   = Local.Recv p l (project g r)
...                                     | no _    | no _    = project g r
...                                     | yes p≡r | yes q≡r = ⊥-elim (p≠q (trans p≡r (sym q≡r)))


record _↔_ { n : ℕ } (g : Global n) (c : Configuration n) : Set where
    field
        isProj : ∀(p : Fin n) -> lookup c p ≡ project g p
