open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Vec using (lookup; _[_]≔_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_; refl; cong)
open import Data.Product using (∃-syntax; _,_)

open import Common using (Label; Action)
open import Global using (Global; _-_→g_)
open import Local using (Local; Configuration; _-_→c_; CComm; _-_→l_)

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

-- TODO: This statement is missing g' ↔ c'
soundness : ∀{ n } { act : Action n } { c g g' }
            -> g ↔ c
            -> g - act →g g'
            -> ∃[ c' ] c - act →c c'
soundness
    {act = act@(.Action.AMsg p q p≠q l)}
    {c = c}
    {g = g@(Global.MsgSingle p q p≠q l g')}
    {g' = .g'}
    assoc
    _-_→g_.GPrefix
    = (c [ p ]≔ (project g' p)) [ q ]≔ (project g' q) , CComm c p≠q lpReduce lqReduce
  where
    lpReduce' : project g p - act →l (project g' p)
    lpReduce' with project g p | p ≟ p | q ≟ p
    ... | res | yes _   | no  _      = _-_→l_.LSend p p≠q
    ... | res | yes _   | yes q=p    = ⊥-elim (p≠q (sym q=p))
    ... | res | no  p≠p | _          = ⊥-elim (p≠p refl)
    lpReduce : lookup c p - act →l (project g' p)
    lpReduce rewrite _↔_.isProj assoc p = lpReduce'
    lqReduce' : project g q - act →l (project g' q)
    lqReduce' with project g q | q ≟ q | p ≟ q
    ... | res | yes _   | no  _      = _-_→l_.LRecv q p≠q
    ... | res | yes _   | yes p=q    = ⊥-elim (p≠q p=q)
    ... | res | no  q≠q | _          = ⊥-elim (q≠q refl)
    lqReduce : lookup c q - act →l (project g' q)
    lqReduce rewrite _↔_.isProj assoc q = lqReduce'
soundness assoc (_-_→g_.GCont gReduce x x₁ x₂ x₃) = {!   !}
{--
soundness
    {n = n}
    {act = .(Action.AMsg p q p≠q l)}
    {c = c}
    {g = g@(Global.MsgSingle p q p≠q l g')}
    {g' = g'}
    assoc
    _-_→g_.GPrefix
    with p ≟ p
... | does Relation.Nullary.because proof with project g p
... | Local.End = {!   !}
... | Local.Send x x₁ res = {!   !}
... | Local.Recv x x₁ res = {!   !}
soundness {n = n} {act = .(Action.AMsg _ _ _ _)} {c = c} {g = .(Global.MsgSingle _ _ _ _ _)} assoc (_-_→g_.GCont gReduce x x₁ x₂ x₃) = {!   !}
--}
