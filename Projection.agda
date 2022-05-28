open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (lookup; _[_]≔_)
open import Data.Vec.Properties using (lookup∘update; lookup∘update′)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_; refl; cong; _≢_; module ≡-Reasoning)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open ≡-Reasoning

open import Common
open import Global
open import Local

private
  variable
    n : ℕ
    t : ℕ
    l : Label
    p q : Fin n
    g gSub : Global n t
    lSub : Local n

project : Global n t -> Fin n -> Local n
project endG _
  = endL
project (msgSingle p q p≢q l gSub) r
  with p ≟ r   | q ≟ r
... | yes _    | no _     = sendSingle q l (project gSub r)
... | no _     | yes _    = recvSingle p l (project gSub r)
... | no _     | no _     = project gSub r
... | yes refl | yes refl = ⊥-elim (p≢q refl)

{-
proj-prefix-other :
  (r s t : Fin n)
  -> ∀{ r≢s }
  -> (gSub : Global n)
  -> r ≢ t
  -> s ≢ t
  -> project (msgSingle r s r≢s l gSub) t ≡ project gSub t
proj-prefix-other r s t _ r≢t s≢t
  with  r ≟ t  | s ≟ t
... | yes refl | _        = ⊥-elim (r≢t refl)
... | _        | yes refl = ⊥-elim (s≢t refl)
... | no _     | no _     = refl

proj-prefix-send :
  (r s : Fin n)
  -> (gSub : Global n)
  -> (r≢s : r ≢ s)
  -> project (msgSingle r s r≢s l gSub) r ≡ sendSingle s l (project gSub r)
proj-prefix-send r s _ r≢s
  with  r ≟ r | s ≟ r
... | yes _   | no _     = refl
... | _       | yes refl = ⊥-elim (r≢s refl)
... | no r≢r  | no _     = ⊥-elim (r≢r refl)

proj-prefix-recv :
  (r s : Fin n)
  -> (gSub : Global n)
  -> (r≢s : r ≢ s)
  -> project (msgSingle r s r≢s l gSub) s ≡ recvSingle r l (project gSub s)
proj-prefix-recv r s _ r≢s
  with  r ≟ s  | s ≟ s
... | no _     | yes _   = refl
... | yes refl | _       = ⊥-elim (r≢s refl)
... | _        | no s≢s  = ⊥-elim (s≢s refl)

record _↔_ { n : ℕ } (g : Global n) (c : Configuration n) : Set where
  field
    isProj : ∀(p : Fin n) -> lookup c p ≡ project g p

open _↔_ public

proj-inv-send :
  project {n} g p ≡ sendSingle q l lSub
  -> ∃[ p≢q ] ∃[ gSub ] g ≡ msgSingle p q p≢q l gSub × project gSub p ≡ lSub
     ⊎
     ∃[ r ] ∃[ s ] ∃[ r≢s ] ∃[ l′ ] ∃[ gSub ]
       g ≡ msgSingle r s r≢s l′ gSub ×
       r ≢ p ×
       s ≢ p ×
       project gSub p ≡ sendSingle q l lSub
proj-inv-send {g = g@endG} projSend = ⊥-elim (endL≢sendSingle projSend)
proj-inv-send {n} {g = g@(msgSingle r s r≢s l′ gSub)} {p} {q} {l} {ltSub} projSend
  with r ≟ p    | s ≟ p
... | yes refl | yes refl = ⊥-elim (r≢s refl)
... | no r≢p   | no s≢p   = inj₂ (r , s , r≢s , l′ , gSub , refl , r≢p , s≢p , projSend)
... | yes refl | no s≢p
      with sendSingle-injective projSend
...     | refl , refl , refl  = inj₁ (r≢s , gSub , refl , refl)

proj-inv-recv :
  project {n} g p ≡ recvSingle q l lSub
  -> ∃[ p≢q ] ∃[ gSub ] g ≡ msgSingle q p p≢q l gSub × project gSub p ≡ lSub
     ⊎
     ∃[ r ] ∃[ s ] ∃[ r≢s ] ∃[ l′ ] ∃[ gSub ]
       g ≡ msgSingle r s r≢s l′ gSub ×
       r ≢ p ×
       s ≢ p ×
       project gSub p ≡ recvSingle q l lSub
proj-inv-recv {g = g@endG} projRecv = ⊥-elim (endL≢recvSingle projRecv)
proj-inv-recv {n} {g = g@(msgSingle r s r≢s l′ gSub)} {p} {q} {l} {lSub} projRecv
  with r ≟ p   | s ≟ p
... | yes refl | yes refl = ⊥-elim (r≢s refl)
... | no r≢p   | no s≢p   = inj₂ (r , s , r≢s , l′ , gSub , refl , r≢p , s≢p , projRecv)
... | no r≢p   | yes refl
      with recvSingle-injective projRecv
...     | refl , refl , refl = inj₁ (r≢s , gSub , refl , refl)

proj-inv-send-recv :
  ∀ { lpSub lqSub }
  -> project {n} g p ≡ sendSingle q l lpSub
  -> project {n} g q ≡ recvSingle p l lqSub
  -> ∃[ p≢q ] ∃[ gSub ] g ≡ msgSingle p q p≢q l gSub × project gSub p ≡ lpSub × project gSub q ≡ lqSub
     ⊎
     ∃[ r ] ∃[ s ] ∃[ r≢s ] ∃[ l′ ] ∃[ gSub ]
       g ≡ msgSingle r s r≢s l′ gSub ×
       r ≢ p ×
       s ≢ p ×
       r ≢ q ×
       s ≢ q ×
       project gSub p ≡ sendSingle q l lpSub ×
       project gSub q ≡ recvSingle p l lqSub
proj-inv-send-recv {n} {g} {p} {q} {l} {lpSub} {lqSub} projSend projRecv
  with proj-inv-send {n} {g} projSend | proj-inv-recv {n} {g} projRecv
... | inj₁ (p≢q₁ , gSub₁ , refl , proj-g₁-p)
    | inj₁ (_ , _ , refl , proj-g₂-q)
        = inj₁ (p≢q₁ , gSub₁ , refl , proj-g₁-p , proj-g₂-q)
proj-inv-send-recv {n} {g} {p} {q} {l} {ltp′} {ltq′} projSend projRecv
    | inj₁ (_ , _ , refl , _)
    | inj₂ (_ , _ , _ , _ , _ , refl , _ , s≢q , _)
        = ⊥-elim (s≢q refl)
proj-inv-send-recv {n} {g} {p} {q} {l} {ltp′} {ltq′} projSend projRecv
    | inj₂ (_ , _ , _ , _ , _ , refl , r≢p , _ , _)
    | inj₁ (_ , _ , refl , _)
        = ⊥-elim (r≢p refl)
proj-inv-send-recv {n} {g} {p} {q} {l} {ltp′} {ltq′} projSend projRecv
    | inj₂ (r , s , r≢s , l′ , gSub₁ , refl , r≢p , s≢p , proj-g₁-p)
    | inj₂ (_ , _ , _   , _  , gSub₂ , refl , r≢q , s≢q , proj-g₂-q)
        = inj₂ (r , s , r≢s , l′ , gSub₁ , refl , r≢p , s≢p , r≢q , s≢q , proj-g₁-p , proj-g₂-q)

config-gt-remove-prefix :
  ∀ { p≢q gSub }
  -> (g : Global n)
  -> (c : Configuration n)
  -> g ↔ c
  -> g ≡ msgSingle p q p≢q l gSub
  -> ∃[ cSub ] cSub ≡ (c [ p ]≔ project gSub p) [ q ]≔ project gSub q × gSub ↔ cSub
config-gt-remove-prefix {n} {p} {q} {_} {p≢q} {gSub} g c assoc refl
  = cSub , refl , (record { isProj = isProj-gSub })
    where
      lpSub = project gSub p
      lqSub = project gSub q
      cSub = (c [ p ]≔ lpSub) [ q ]≔ lqSub
      isProj-gSub : ∀ (r : Fin n) -> lookup cSub r ≡ project gSub r
      isProj-gSub r
        with p ≟ r    | q ≟ r
      ... | yes refl | yes refl = ⊥-elim (p≢q refl)
      ... | yes refl | no  _
          rewrite lookup∘update′ p≢q (c [ p ]≔ lpSub) lqSub
          rewrite lookup∘update p c lpSub
          = refl
      ... | no _    | yes refl
          rewrite lookup∘update q (c [ p ]≔ lpSub) lqSub
          = refl
      ... | no p≢r  | no  q≢r
          rewrite lookup∘update′ (¬≡-flip q≢r) (c [ p ]≔ lpSub) lqSub
          rewrite lookup∘update′ (¬≡-flip p≢r) c lpSub
          rewrite isProj assoc r
          = proj-prefix-other p q r gSub p≢r q≢r

  -}