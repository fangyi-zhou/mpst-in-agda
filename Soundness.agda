open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Vec using (lookup; _[_]≔_)
open import Data.Vec.Properties using ([]≔-commutes; []≔-idempotent; []≔-lookup)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_; refl; cong; _≢_; module ≡-Reasoning)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open ≡-Reasoning

open import Common
open import Global
open import Local
open import Projection

soundness :
  ∀ { n ℓ : ℕ } { act : Action n ℓ } { c g g′ }
  -> g ↔ c
  -> g - act →g g′
  -> ∃[ c′ ] c - act →c c′ × g′ ↔ c′
soundness
  {n = n}
  {act = act@(action .p .q p≢q .l)}
  {c = c}
  {g = g@(msgSingle p q p≢q-gt l g′)}
  {g′ = .g′}
  assoc
  →g-prefix
  = c′ , (→c-comm c p≢q refl refl refl lpReduce lqReduce , g′↔c′)
  where
    config-without-prefix = config-gt-remove-prefix g c assoc refl
    c′ = proj₁ config-without-prefix
    g′↔c′ : g′ ↔ c′
    g′↔c′ = proj₂ (proj₂ config-without-prefix)
    lpReduce : (p , lookup c p) - act →l (p , project g′ p)
    lpReduce rewrite isProj assoc p
      = →l-send p (proj-prefix-send p q g′ p≢q-gt) p≢q
    lqReduce : (q , lookup c q) - act →l (q , project g′ q)
    lqReduce rewrite isProj assoc q
      = →l-recv q (proj-prefix-recv p q g′ p≢q-gt) p≢q
soundness
  {n = n}
  {ℓ = ℓ}
  {act = act@(.action p q p≢q l)}
  {c = c}
  {g = g@(msgSingle r s r≢s l′ gSub)}
  {g′ = g′@(.msgSingle r s r≢s l′ gSub′)}
  assoc
  (→g-cont gReduce p≢r q≢r p≢s q≢s)
  = c′ , cReduce , assoc′
  where
    config-without-prefix = config-gt-remove-prefix g c assoc refl
    cSub = proj₁ config-without-prefix
    gSub↔cSub : gSub ↔ cSub
    gSub↔cSub = proj₂ (proj₂ config-without-prefix)
    soundness-gSub : ∃[ cSub′ ] cSub - act →c cSub′ × gSub′ ↔ cSub′
    soundness-gSub = soundness gSub↔cSub gReduce
    c′ : Configuration n ℓ
    c′ with soundness-gSub
    ... | cSub′ , _ , _ = (cSub′ [ r ]≔ lr′) [ s ]≔ ls′
      where
        lr′ : Local n ℓ
        lr′ with soundness-gSub
        ...   | cSub′ , _ , _ = sendSingle s l′ (lookup cSub′ r)
        ls′ : Local n ℓ
        ls′ with soundness-gSub
        ...   | cSub′ , _ , _ = recvSingle r l′ (lookup cSub′ s)
    isProj-g′ : ∀(t : Fin n) -> lookup c′ t ≡ project g′ t
    isProj-g′ t with soundness-gSub
    ...   | cSub′ , _ , gSub′↔cSub′
        with r ≟ t   | s ≟ t
    ...   | yes r≡t  | no _
        rewrite sym r≡t
        rewrite lookup-update₂-left cSub′ r s r≢s (sendSingle s l′ (lookup cSub′ r)) (recvSingle r l′ (lookup cSub′ s))
        rewrite isProj gSub′↔cSub′ r = refl
    ...   | no _     | yes s≡t
        rewrite sym s≡t
        rewrite lookup-update₂-right cSub′ r s (sendSingle s l′ (lookup cSub′ r)) (recvSingle r l′ (lookup cSub′ s))
        rewrite isProj gSub′↔cSub′ s = refl
    ...   | no r≢t   | no s≢t
        rewrite lookup-update₂-other cSub′ r s t (¬≡-flip r≢t) (¬≡-flip s≢t) (sendSingle s l′ (lookup cSub′ r)) (recvSingle r l′ (lookup cSub′ s))
        rewrite isProj gSub′↔cSub′ t = refl
    ...   | yes refl | yes refl = ⊥-elim (r≢s refl)
    assoc′ : g′ ↔ c′
    assoc′ = record { isProj = isProj-g′ }
    cReduce : c - act →c c′
    cReduce with soundness-gSub
    ...   | cSub′ , →c-comm {lp = lp} {lp′ = lp′} {lq = lq} {lq′ = lq′} .cSub .p≢q refl refl refl lpReduce lqReduce , gSub′↔cSub′
            = →c-comm c p≢q lp≡c[p] lq≡c[q] c→c′ lpReduce lqReduce
      where
        lr′ = sendSingle s l′ (lookup cSub′ r)
        ls′ = recvSingle r l′ (lookup cSub′ s)
        lp≡c[p] : lp ≡ lookup c p
        lp≡c[p]
          rewrite lookup-update₂-other c r s p p≢r p≢s (project gSub r) (project gSub s) = refl
        lq≡c[q] : lq ≡ lookup c q
        lq≡c[q]
          rewrite lookup-update₂-other c r s q q≢r q≢s (project gSub r) (project gSub s) = refl
        lr′≡c[r] : lr′ ≡ lookup c r
        lr′≡c[r]
          rewrite lookup-update₂-other cSub p q r (¬≡-flip p≢r) (¬≡-flip q≢r) lp′ lq′
          rewrite isProj assoc r
          rewrite proj-prefix-send {l = l′} r s gSub r≢s
          rewrite lookup-update₂-left c r s r≢s (project gSub r) (project gSub s)
          = refl
        ls′≡c[s] : ls′ ≡ lookup c s
        ls′≡c[s]
          rewrite lookup-update₂-other cSub p q s (¬≡-flip p≢s) (¬≡-flip q≢s) lp′ lq′
          rewrite isProj assoc s
          rewrite proj-prefix-recv {l = l′} r s gSub r≢s
          rewrite lookup-update₂-right c r s (project gSub r) (project gSub s)
          = refl
        c→c′ : (cSub′ [ r ]≔ lr′) [ s ]≔ ls′ ≡ (c [ p ]≔ lp′) [ q ]≔ lq′
        c→c′
          rewrite []≔-commutes {x = lr′} {y = ls′} ((((c [ r ]≔ project gSub r) [ s ]≔ project gSub s) [ p ]≔ lp′) [ q ]≔ lq′) r s r≢s
          rewrite []≔-commutes {x = lq′} {y = ls′} (((c [ r ]≔ project gSub r) [ s ]≔ project gSub s) [ p ]≔ lp′) q s q≢s
          rewrite []≔-commutes {x = lp′} {y = ls′} ((c [ r ]≔ project gSub r) [ s ]≔ project gSub s) p s p≢s
          rewrite []≔-idempotent {x = project gSub s} {y = ls′} (c [ r ]≔ project gSub r) s
          rewrite []≔-commutes {x = lq′} {y = lr′} (((c [ r ]≔ project gSub r) [ s ]≔ ls′) [ p ]≔ lp′) q r q≢r
          rewrite []≔-commutes {x = lp′} {y = lr′} ((c [ r ]≔ project gSub r) [ s ]≔ ls′) p r p≢r
          rewrite []≔-commutes {x = ls′} {y = lr′} (c [ r ]≔ project gSub r) s r (¬≡-flip r≢s)
          rewrite []≔-idempotent {x = project gSub r} {y = lr′} c r
          rewrite lr′≡c[r]
          rewrite ls′≡c[s]
          rewrite []≔-lookup c r
          rewrite []≔-lookup c s
          = refl
