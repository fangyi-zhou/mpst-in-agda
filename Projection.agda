open import Level using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Vec using (lookup; _[_]≔_)
open import Data.Vec.Properties using (lookup∘update; lookup∘update′; []≔-commutes; []≔-idempotent; []≔-lookup)
open import Function.Base using (const)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_; refl; cong; _≢_; module ≡-Reasoning)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open ≡-Reasoning

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

¬≡-flip : ∀{l} { A : Set l } { x y : A } -> (x ≢ y) -> (y ≢ x)
¬≡-flip x≢y = λ y≡x → x≢y (sym y≡x)

proj-prefix-other : ∀{ n : ℕ }
                 -> (r s t : Fin n)
                 -> ∀{ r≠s l }
                 -> (g' : Global n)
                 -> r ≢ t
                 -> s ≢ t
                 -> project (Global.MsgSingle r s r≠s l g') t ≡ project g' t
proj-prefix-other r s t _ r≠t s≠t with  r ≟ t   | s ≟ t
...                                   | yes r≡t | _       = ⊥-elim (r≠t r≡t)
...                                   | _       | yes s≡t = ⊥-elim (s≠t s≡t)
...                                   | no _    | no _    = refl

proj-prefix-send : ∀{ n : ℕ }
                 -> (r s : Fin n)
                 -> ∀{ l }
                 -> (g' : Global n)
                 -> (r≠s : r ≢ s)
                 -> project (Global.MsgSingle r s r≠s l g') r ≡ Local.Send s l (project g' r)
proj-prefix-send r s _ r≠s with  r ≟ r   | s ≟ r
...                            | yes _   | no _    = refl
...                            | _       | yes s≡r = ⊥-elim (r≠s (sym s≡r))
...                            | no r≠r  | no _    = ⊥-elim (r≠r refl)

proj-prefix-recv : ∀{ n : ℕ }
                 -> (r s : Fin n)
                 -> ∀{ l }
                 -> (g' : Global n)
                 -> (r≠s : r ≢ s)
                 -> project (Global.MsgSingle r s r≠s l g') s ≡ Local.Recv r l (project g' s)
proj-prefix-recv r s _ r≠s with  r ≟ s   | s ≟ s
...                            | no _    | yes _   = refl
...                            | yes r≡s | _       = ⊥-elim (r≠s r≡s)
...                            | _       | no s≠s  = ⊥-elim (s≠s refl)

record _↔_ { n : ℕ } (g : Global n) (c : Configuration n) : Set where
    field
        isProj : ∀(p : Fin n) -> lookup c p ≡ project g p

soundness : ∀{ n } { act : Action n } { c g g' }
            -> g ↔ c
            -> g - act →g g'
            -> ∃[ c' ] ((c - act →c c') × (g' ↔ c'))
soundness
    {n = n}
    {act = act@(.Action.AMsg p q p≠q l)}
    {c = c}
    {g = g@(Global.MsgSingle p q p≠q l g')}
    {g' = .g'}
    assoc
    _-_→g_.GPrefix
    = c' , (CComm c p≠q refl refl refl lpReduce lqReduce , assoc')
  where
    c'' : Configuration n
    c'' = c [ p ]≔ (project g' p)
    c' : Configuration n
    c' = c'' [ q ]≔ (project g' q)
    lpReduce' : project g p - act →l (project g' p)
    lpReduce' with p ≟ p   | q ≟ p
    ...          | yes _   | no  _   = _-_→l_.LSend p p≠q
    ...          | yes _   | yes q=p = ⊥-elim (p≠q (sym q=p))
    ...          | no  p≠p | _       = ⊥-elim (p≠p refl)
    lpReduce : lookup c p - act →l (project g' p)
    lpReduce rewrite _↔_.isProj assoc p = lpReduce'
    lqReduce' : project g q - act →l (project g' q)
    lqReduce' with q ≟ q   | p ≟ q
    ...          | yes _   | no  _   = _-_→l_.LRecv q p≠q
    ...          | yes _   | yes p=q = ⊥-elim (p≠q p=q)
    ...          | no  q≠q | _       = ⊥-elim (q≠q refl)
    lqReduce : lookup c q - act →l (project g' q)
    lqReduce rewrite _↔_.isProj assoc q = lqReduce'
    isProj-g' : (r : Fin n) -> lookup c' r ≡ project g' r
    isProj-g' r with p ≟ r   | q ≟ r
    ...            | yes p≡r | yes q≡r = ⊥-elim (p≠q (trans p≡r (sym q≡r)))
    ...            | yes p≡r | no  _   rewrite (sym p≡r)
                                       rewrite lookup∘update′ p≠q c'' (project g' q) = lookup∘update p c (project g' p)
    ...            | no _    | yes q≡r rewrite (sym q≡r) = lookup∘update q c'' (project g' q)
    ...            | no p≠r  | no  q≠r rewrite lookup∘update′ (¬≡-flip q≠r) c'' (project g' q)
                                       rewrite lookup∘update′ (¬≡-flip p≠r) c   (project g' p)
                                       rewrite _↔_.isProj assoc r = proj-prefix-other p q r g' p≠r q≠r
    assoc' : g' ↔ c'
    assoc' = record { isProj = isProj-g' }
soundness
    {n = n}
    {act = act@(.Action.AMsg p q p≠q l)}
    {c = c}
    {g = g@(Global.MsgSingle r s r≠s l' g₁)}
    {g' = g'@(.Global.MsgSingle r s r≠s l' g₂)}
    assoc
    (_-_→g_.GCont gReduce p≠r q≠r p≠s q≠s)
    = c' , (cReduce , assoc')
  where
    cSub' : Configuration n
    cSub' = c [ r ]≔ (project g₁ r)
    cSub : Configuration n
    cSub = cSub' [ s ]≔ (project g₁ s)
    lookup-cSub-r : lookup cSub r ≡ project g₁ r
    lookup-cSub-r rewrite lookup∘update′ r≠s cSub' (project g₁ s)
                  rewrite lookup∘update r c (project g₁ r) = refl
    lookup-cSub-s : lookup cSub s ≡ project g₁ s
    lookup-cSub-s rewrite lookup∘update s cSub' (project g₁ s) = refl
    lookup-cSub-t : (t : Fin n) -> r ≢ t -> s ≢ t -> lookup cSub t ≡ project g₁ t
    lookup-cSub-t t r≠t s≠t rewrite lookup∘update′ (¬≡-flip s≠t) cSub' (project g₁ s)
                            rewrite lookup∘update′ (¬≡-flip r≠t) c     (project g₁ r)
                            rewrite sym (proj-prefix-other r s t g₁ r≠t s≠t) = _↔_.isProj assoc t
    isProj-g₁ : ∀(t : Fin n) -> lookup cSub t ≡ project g₁ t
    isProj-g₁ t with r ≟ t   | s ≟ t
    ...            | yes r≡t | no _    rewrite (sym r≡t) = lookup-cSub-r
    ...            | no _    | yes s≡t rewrite (sym s≡t) = lookup-cSub-s
    ...            | no r≠t  | no s≠t  = lookup-cSub-t t r≠t s≠t
    ...            | yes r≡t | yes s≡t = ⊥-elim (r≠s (trans r≡t (sym s≡t)))
    g₁↔cSub : g₁ ↔ cSub
    g₁↔cSub = record { isProj = isProj-g₁ }
    ∃c'Sub : ∃[ c'Sub ] (cSub - act →c c'Sub × g₂ ↔ c'Sub)
    ∃c'Sub = soundness g₁↔cSub gReduce
    c'Sub : Configuration n
    c'Sub = proj₁ ∃c'Sub
    cSubReduce : cSub - act →c c'Sub
    cSubReduce = proj₁ (proj₂ ∃c'Sub)
    assocSub : g₂ ↔ c'Sub
    assocSub = proj₂ (proj₂ ∃c'Sub)
    lr' : Local n
    lr' = Local.Send s l' (lookup c'Sub r)
    c'' : Configuration n
    c'' = c'Sub [ r ]≔ lr'
    ls' : Local n
    ls' = Local.Recv r l' (lookup c'Sub s)
    c' : Configuration n
    c' = c'' [ s ]≔ ls'
    isProj-g' : ∀(t : Fin n) -> lookup c' t ≡ project g' t
    isProj-g' t with r ≟ t   | s ≟ t
    ...            | yes r≡t | no _    rewrite (sym r≡t)
                                       rewrite lookup∘update′ r≠s c'' ls'
                                       rewrite lookup∘update r c'Sub lr'
                                       rewrite _↔_.isProj assocSub r = refl
    ...            | no _    | yes s≡t rewrite (sym s≡t)
                                       rewrite lookup∘update s c'' ls'
                                       rewrite _↔_.isProj assocSub s = refl
    ...            | no r≠t  | no s≠t  rewrite lookup∘update′ (¬≡-flip s≠t) c'' ls'
                                       rewrite lookup∘update′ (¬≡-flip r≠t) c'Sub lr'
                                       rewrite _↔_.isProj assocSub t = refl
    ...            | yes r≡t | yes s≡t = ⊥-elim (r≠s (trans r≡t (sym s≡t)))
    assoc' : g' ↔ c'
    assoc' = record { isProj = isProj-g' }
    cReduce : c - act →c c'
    cReduce with cSubReduce
    ... | CComm {lp = lp} {lp' = lp'} {lq = lq} {lq' = lq'} .cSub .p≠q lp≡cSub[p] lq≡cSub[q] cSub→c'Sub lpReduce lqReduce =
            CComm {n} {p} {q} {l} {lp} {lp'} {lq} {lq'} {c'} c p≠q lp≡c[p] lq≡c[q] c→c' lpReduce lqReduce
      where
        lp≡c[p] : lp ≡ lookup c p
        lp≡c[p] rewrite lp≡cSub[p]
                rewrite lookup∘update′ p≠s cSub' (project g₁ s)
                rewrite lookup∘update′ p≠r c (project g₁ r) = refl
        lq≡c[q] : lq ≡ lookup c q
        lq≡c[q] rewrite lq≡cSub[q]
                rewrite lookup∘update′ q≠s cSub' (project g₁ s)
                rewrite lookup∘update′ q≠r c (project g₁ r) = refl
        lr'≡c[r] : lr' ≡ lookup c r
        lr'≡c[r] = begin
                     Local.Send s l' (lookup c'Sub r)
                   ≡⟨ cong (λ c'Sub -> Local.Send s l' (lookup c'Sub r)) cSub→c'Sub ⟩
                     Local.Send s l' (lookup ((cSub [ p ]≔ lp') [ q ]≔ lq') r)
                   ≡⟨ cong (λ ls'' -> Local.Send s l' ls'') (lookup∘update′ (¬≡-flip q≠r) (cSub [ p ]≔ lp') lq') ⟩
                     Local.Send s l' (lookup (cSub [ p ]≔ lp') r)
                   ≡⟨ cong (λ ls'' -> Local.Send s l' ls'') (lookup∘update′ (¬≡-flip p≠r) cSub lp') ⟩
                     Local.Send s l' (lookup cSub r)
                   ≡⟨ cong (λ ls'' -> Local.Send s l' ls'') (isProj-g₁ r) ⟩
                     Local.Send s l' (project g₁ r)
                   ≡˘⟨ proj-prefix-send r s g₁ r≠s ⟩
                     project g r
                   ≡⟨ sym (_↔_.isProj assoc r) ⟩
                     lookup c r
                   ∎
        ls'≡c[s] : ls' ≡ lookup c s
        ls'≡c[s] = begin
                     Local.Recv r l' (lookup c'Sub s)
                   ≡⟨ cong (λ c'Sub -> Local.Recv r l' (lookup c'Sub s)) cSub→c'Sub ⟩
                     Local.Recv r l' (lookup ((cSub [ p ]≔ lp') [ q ]≔ lq') s)
                   ≡⟨ cong (λ ls'' -> Local.Recv r l' ls'') (lookup∘update′ (¬≡-flip q≠s) (cSub [ p ]≔ lp') lq') ⟩
                     Local.Recv r l' (lookup (cSub [ p ]≔ lp') s)
                   ≡⟨ cong (λ ls'' -> Local.Recv r l' ls'') (lookup∘update′ (¬≡-flip p≠s) cSub lp') ⟩
                     Local.Recv r l' (lookup cSub s)
                   ≡⟨ cong (λ ls'' -> Local.Recv r l' ls'') (isProj-g₁ s) ⟩
                     Local.Recv r l' (project g₁ s)
                   ≡˘⟨ proj-prefix-recv r s g₁ r≠s ⟩
                     project g s
                   ≡⟨ sym (_↔_.isProj assoc s) ⟩
                     lookup c s
                   ∎
        c→c' : ((c'Sub [ r ]≔ lr') [ s ]≔ ls') ≡ ((c [ p ]≔ lp') [ q ]≔ lq')
        c→c' = begin
                 (c'Sub [ r ]≔ lr') [ s ]≔ ls'
               ≡⟨ cong (λ v -> (v [ r ]≔ lr') [ s ]≔ ls') cSub→c'Sub ⟩
                 (((cSub [ p ]≔ lp') [ q ]≔ lq') [ r ]≔ lr') [ s ]≔ ls'
               ≡⟨⟩
                 (((((c [ r ]≔ project g₁ r) [ s ]≔ project g₁ s) [ p ]≔ lp') [ q ]≔ lq') [ r ]≔ lr') [ s ]≔ ls'
               ≡⟨ []≔-commutes ((((c [ r ]≔ project g₁ r) [ s ]≔ project g₁ s) [ p ]≔ lp') [ q ]≔ lq') r s r≠s ⟩
                 (((((c [ r ]≔ project g₁ r) [ s ]≔ project g₁ s) [ p ]≔ lp') [ q ]≔ lq') [ s ]≔ ls') [ r ]≔ lr'
               ≡⟨ cong (λ v -> v [ r ]≔ lr') ([]≔-commutes (((c [ r ]≔ project g₁ r) [ s ]≔ project g₁ s) [ p ]≔ lp') q s q≠s) ⟩
                 (((((c [ r ]≔ project g₁ r) [ s ]≔ project g₁ s) [ p ]≔ lp') [ s ]≔ ls') [ q ]≔ lq') [ r ]≔ lr'
               ≡⟨ cong (λ v -> (v [ q ]≔ lq') [ r ]≔ lr') ([]≔-commutes ((c [ r ]≔ project g₁ r) [ s ]≔ project g₁ s) p s p≠s) ⟩
                 (((((c [ r ]≔ project g₁ r) [ s ]≔ project g₁ s) [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq') [ r ]≔ lr'
               ≡⟨ cong (λ v -> ((v [ p ]≔ lp') [ q ]≔ lq') [ r ]≔ lr') ([]≔-idempotent (c [ r ]≔ project g₁ r) s) ⟩
                 ((((c [ r ]≔ project g₁ r) [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq') [ r ]≔ lr'
               ≡⟨ []≔-commutes (((c [ r ]≔ project g₁ r) [ s ]≔ ls') [ p ]≔ lp') q r q≠r ⟩
                 ((((c [ r ]≔ project g₁ r) [ s ]≔ ls') [ p ]≔ lp') [ r ]≔ lr') [ q ]≔ lq'
               ≡⟨ cong (λ v -> v [ q ]≔ lq') ([]≔-commutes ((c [ r ]≔ project g₁ r) [ s ]≔ ls') p r p≠r) ⟩
                 ((((c [ r ]≔ project g₁ r) [ s ]≔ ls') [ r ]≔ lr') [ p ]≔ lp') [ q ]≔ lq'
               ≡⟨ cong (λ v -> (v [ p ]≔ lp') [ q ]≔ lq') ([]≔-commutes (c [ r ]≔ project g₁ r) s r (¬≡-flip r≠s)) ⟩
                 ((((c [ r ]≔ project g₁ r) [ r ]≔ lr') [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq'
               ≡⟨ cong (λ v -> ((v [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq') ([]≔-idempotent c r) ⟩
                 (((c [ r ]≔ lr') [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq'
               ≡⟨ cong (λ c[r] -> (((c [ r ]≔ c[r]) [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq') lr'≡c[r] ⟩
                 (((c [ r ]≔ lookup c r) [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq'
               ≡⟨ cong (λ v -> ((v [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq') ([]≔-lookup c r) ⟩
                 ((c [ s ]≔ ls') [ p ]≔ lp') [ q ]≔ lq'
               ≡⟨ cong (λ c[s] -> ((c [ s ]≔ c[s]) [ p ]≔ lp') [ q ]≔ lq') ls'≡c[s] ⟩
                 ((c [ s ]≔ lookup c s) [ p ]≔ lp') [ q ]≔ lq'
               ≡⟨ cong (λ v -> (v [ p ]≔ lp') [ q ]≔ lq') ([]≔-lookup c s) ⟩
                 (c [ p ]≔ lp') [ q ]≔ lq'
               ∎
