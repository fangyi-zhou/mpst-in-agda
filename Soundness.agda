{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Vec using (lookup; _[_]≔_)
open import Data.Vec.Properties using (lookup∘update; lookup∘update′; []≔-commutes; []≔-idempotent; []≔-lookup)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_; refl; cong; _≢_; module ≡-Reasoning)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open ≡-Reasoning

open import Common
open import Global
open import Local
open import Projection

soundness :
  ∀ { n : ℕ } { act : Action n } { c g g′ }
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
    c′ : Configuration n
    c′ with soundness-gSub
    ... | cSub′ , _ , _ = (cSub′ [ r ]≔ lr′) [ s ]≔ ls′
      where
        lr′ : Local n
        lr′ with soundness-gSub
        ...   | cSub′ , _ , _ = sendSingle s l′ (lookup cSub′ r)
        ls′ : Local n
        ls′ with soundness-gSub
        ...   | cSub′ , _ , _ = recvSingle r l′ (lookup cSub′ s)
    isProj-g′ : ∀(t : Fin n) -> lookup c′ t ≡ project g′ t
    isProj-g′ t with soundness-gSub
    ...   | cSub′ , _ , gSub′↔cSub′
        with r ≟ t   | s ≟ t
    ...   | yes r≡t  | no _
        rewrite sym r≡t
        rewrite lookup∘update′ r≢s (cSub′ [ r ]≔ sendSingle s l′ (lookup cSub′ r)) (recvSingle r l′ (lookup cSub′ s))
        rewrite lookup∘update r cSub′ (sendSingle s l′ (lookup cSub′ r))
        rewrite isProj gSub′↔cSub′ r = refl
    ...   | no _     | yes s≡t
        rewrite sym s≡t
        rewrite lookup∘update s (cSub′ [ r ]≔ sendSingle s l′ (lookup cSub′ r)) (recvSingle r l′ (lookup cSub′ s))
        rewrite isProj gSub′↔cSub′ s = refl
    ...   | no r≢t   | no s≢t
        rewrite lookup∘update′ (¬≡-flip s≢t) (cSub′ [ r ]≔ sendSingle s l′ (lookup cSub′ r)) (recvSingle r l′ (lookup cSub′ s))
        rewrite lookup∘update′ (¬≡-flip r≢t) cSub′ (sendSingle s l′ (lookup cSub′ r))
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
          rewrite lookup∘update′ p≢s (c [ r ]≔ project gSub r) (project gSub s)
          rewrite lookup∘update′ p≢r c (project gSub r) = refl
        lq≡c[q] : lq ≡ lookup c q
        lq≡c[q]
          rewrite lookup∘update′ q≢s (c [ r ]≔ project gSub r) (project gSub s)
          rewrite lookup∘update′ q≢r c (project gSub r) = refl
        lr′≡c[r] : lr′ ≡ lookup c r
        lr′≡c[r]
          rewrite lookup∘update′ (¬≡-flip q≢r) (cSub [ p ]≔ lp′) lq′
          rewrite lookup∘update′ (¬≡-flip p≢r) cSub lp′
          rewrite isProj assoc r
          rewrite proj-prefix-send {l = l′} r s gSub r≢s
          rewrite lookup∘update′ r≢s (c [ r ]≔ project gSub r) (project gSub s)
          rewrite lookup∘update r c (project gSub r)
          = refl
        ls′≡c[s] : ls′ ≡ lookup c s
        ls′≡c[s]
          rewrite lookup∘update′ (¬≡-flip q≢s) (cSub [ p ]≔ lp′) lq′
          rewrite lookup∘update′ (¬≡-flip p≢s) cSub lp′
          rewrite isProj assoc s
          rewrite proj-prefix-recv {l = l′} r s gSub r≢s
          rewrite lookup∘update s (c [ r ]≔ project gSub r) (project gSub s)
          = refl
        c→c′ : (cSub′ [ r ]≔ lr′) [ s ]≔ ls′ ≡ (c [ p ]≔ lp′) [ q ]≔ lq′
        c→c′
          rewrite []≔-commutes ((((c [ r ]≔ project gSub r) [ s ]≔ project gSub s) [ p ]≔ lp′) [ q ]≔ lq′) r s {lr′} {ls′} r≢s
          rewrite []≔-commutes (((c [ r ]≔ project gSub r) [ s ]≔ project gSub s) [ p ]≔ lp′) q s {lq′} {ls′} q≢s
          rewrite []≔-commutes ((c [ r ]≔ project gSub r) [ s ]≔ project gSub s) p s {lp′} {ls′} p≢s
          rewrite []≔-idempotent (c [ r ]≔ project gSub r) s {project gSub s} {ls′}
          rewrite []≔-commutes (((c [ r ]≔ project gSub r) [ s ]≔ ls′) [ p ]≔ lp′) q r {lq′} {lr′} q≢r
          rewrite []≔-commutes ((c [ r ]≔ project gSub r) [ s ]≔ ls′) p r {lp′} {lr′} p≢r
          rewrite []≔-commutes (c [ r ]≔ project gSub r) s r {ls′} {lr′} (¬≡-flip r≢s)
          rewrite []≔-idempotent c r {project gSub r} {lr′}
          rewrite lr′≡c[r]
          rewrite ls′≡c[s]
          rewrite []≔-lookup c r
          rewrite []≔-lookup c s
          = refl
