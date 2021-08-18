open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Vec using (lookup; _[_]≔_)
open import Data.Vec.Properties using (lookup∘updateAt; lookup∘updateAt′)
open import Function.Base using (const)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_; refl; cong; _≢_)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂)
open import Level using (Level)

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

¬≡-flip : ∀ { A B : Set } -> (A ≢ B) -> (B ≢ A)
¬≡-flip a≢b = λ b≡a → a≢b (sym b≡a)

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
    lpReduce' with project g p | p ≟ p   | q ≟ p
    ...          | _           | yes _   | no  _   = _-_→l_.LSend p p≠q
    ...          | _           | yes _   | yes q=p = ⊥-elim (p≠q (sym q=p))
    ...          | _           | no  p≠p | _       = ⊥-elim (p≠p refl)
    lpReduce : lookup c p - act →l (project g' p)
    lpReduce rewrite _↔_.isProj assoc p = lpReduce'
    lqReduce' : project g q - act →l (project g' q)
    lqReduce' with project g q | q ≟ q   | p ≟ q
    ...          | _           | yes _   | no  _   = _-_→l_.LRecv q p≠q
    ...          | _           | yes _   | yes p=q = ⊥-elim (p≠q p=q)
    ...          | _           | no  q≠q | _       = ⊥-elim (q≠q refl)
    lqReduce : lookup c q - act →l (project g' q)
    lqReduce rewrite _↔_.isProj assoc q = lqReduce'
soundness
    {n = n}
    {act = act@(.Action.AMsg p q p≠q l)}
    {c = c}
    {g = g@(Global.MsgSingle r s r≠s l' g₁)}
    {g' = g'@(.Global.MsgSingle r s r≠s l' g₂)}
    assoc
    (_-_→g_.GCont gReduce p≠r q≠r p≠s q≠s)
    = c' , cReduce
  where
    cSub' : Configuration n
    cSub' = c [ r ]≔ (project g₁ r)
    cSub : Configuration n
    cSub = cSub' [ s ]≔ (project g₁ s)
    lookup-r-1 : lookup cSub' r ≡ project g₁ r
    lookup-r-1 = lookup∘updateAt r c
    lookup-r-2 : lookup cSub r ≡ lookup cSub' r
    lookup-r-2 = lookup∘updateAt′ r s r≠s cSub'
    lookup-cSub-r : lookup cSub r ≡ project g₁ r
    lookup-cSub-r rewrite lookup-r-2 rewrite lookup-r-1 = refl
    lookup-s : lookup cSub s ≡ project g₁ s
    lookup-s = lookup∘updateAt s cSub'
    lookup-cSub-s : lookup cSub s ≡ project g₁ s
    lookup-cSub-s rewrite lookup-s = refl
    proj-t : (t : Fin n) -> r ≢ t -> s ≢ t -> project g t ≡ project g₁ t
    proj-t t r≠t s≠t with project g t | r ≟ t   | s ≟ t
    ...                 | _           | yes r≡t | _       = ⊥-elim (r≠t r≡t)
    ...                 | _           | _       | yes s≡t = ⊥-elim (s≠t s≡t)
    ...                 | _           | no _    | no _    = refl
    lookup-t-1 : (t : Fin n) -> r ≢ t -> lookup cSub' t ≡ lookup c t
    lookup-t-1 t r≠t = lookup∘updateAt′ t r (λ t≡r -> r≠t (sym t≡r)) c
    lookup-t-2 : (t : Fin n) -> s ≢ t -> lookup cSub t ≡ lookup cSub' t
    lookup-t-2 t s≠t = lookup∘updateAt′ t s (λ t≡s -> s≠t (sym t≡s)) cSub'
    lookup-cSub-t : (t : Fin n) -> r ≢ t -> s ≢ t -> lookup cSub t ≡ project g₁ t
    lookup-cSub-t t r≠t s≠t rewrite lookup-t-2 t s≠t rewrite lookup-t-1 t r≠t rewrite sym (proj-t t r≠t s≠t) = _↔_.isProj assoc t
    isProj-g₁ : ∀( t : Fin n ) -> lookup cSub t ≡ project g₁ t
    isProj-g₁ t with r ≟ t   | s ≟ t
    ...            | yes r≡t | no _    rewrite (sym r≡t) = lookup-cSub-r
    ...            | no _    | yes s≡t rewrite (sym s≡t) = lookup-cSub-s
    ...            | no r≠t  | no s≠t  = lookup-cSub-t t r≠t s≠t
    ...            | yes r≡t | yes s≡t = ⊥-elim (r≠s (trans r≡t (sym s≡t)))
    g₁↔cSub : g₁ ↔ cSub
    g₁↔cSub = record { isProj = isProj-g₁ }
    ∃c'Sub : ∃[ c'Sub ] cSub - act →c c'Sub
    ∃c'Sub = soundness g₁↔cSub gReduce
    c'Sub : Configuration n
    c'Sub = proj₁ ∃c'Sub
    cSubReduce : cSub - act →c c'Sub
    cSubReduce = proj₂ ∃c'Sub
    c'' : Configuration n
    c'' = c [ r ]≔ (Local.Send s l' (lookup c'Sub r))
    c' : Configuration n
    c' = c'' [ s ]≔ (Local.Recv r l' (lookup c'Sub s))
    postulate cReduce : c - act →c c'
