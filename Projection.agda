open import Data.Empty using (⊥-elim)
open import Data.Bool using (true; false)
open import Data.Maybe using (just)
open import Data.Nat using (_≟_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_)
open import Data.Nat.Properties using (<-strictTotalOrder)
import Data.Tree.AVL <-strictTotalOrder as Map
import Data.Tree.AVL.Sets <-strictTotalOrder as Sets
open Map using (_,_)

open import Common using (Role; Label)
open import Global using (Global; roles)
open import Local using (Local; Configuration)

project : Global -> Role -> Local
project Global.End r = Local.End
project (Global.MsgSingle p q p≠q l g) r with p ≟ r | q ≟ r
...                                     | yes _   | no _    = Local.Send q l (project g r)
...                                     | no _    | yes _   = Local.Recv p l (project g r)
...                                     | no _    | no _    = project g r
...                                     | yes p≡r | yes q≡r = ⊥-elim (p≠q (trans p≡r (sym q≡r)))


record _↔_ (g : Global) (c : Configuration) : Set where
    field
        hasRoles : ∀(p : Role) -> (p Sets.∈? (roles g)) ≡ true -> (p Map.∈? c) ≡ true
        isProj : ∀{ l } -> ∀(p : Role) -> Map.lookup p c ≡ just l -> l ≡ project g p
