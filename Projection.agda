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

project : ∀ { n : ℕ } -> Global n -> Fin n -> Local n
project endG _
    = endL
project (msgSingle p q p≠q l g) r
    with p ≟ r | q ≟ r
...  | yes _   | no _    = sendSingle q l (project g r)
...  | no _    | yes _   = recvSingle p l (project g r)
...  | no _    | no _    = project g r
...  | yes p≡r | yes q≡r = ⊥-elim (p≠q (trans p≡r (sym q≡r)))

proj-prefix-other :
    ∀ { n : ℕ }
    -> (r s t : Fin n)
    -> ∀{ r≠s l }
    -> (g' : Global n)
    -> r ≢ t
    -> s ≢ t
    -> project (msgSingle r s r≠s l g') t ≡ project g' t
proj-prefix-other r s t _ r≠t s≠t
    with  r ≟ t   | s ≟ t
...     | yes r≡t | _       = ⊥-elim (r≠t r≡t)
...     | _       | yes s≡t = ⊥-elim (s≠t s≡t)
...     | no _    | no _    = refl

proj-prefix-send :
    ∀ { n : ℕ }
    -> (r s : Fin n)
    -> ∀ { l }
    -> (g' : Global n)
    -> (r≠s : r ≢ s)
    -> project (msgSingle r s r≠s l g') r ≡ sendSingle s l (project g' r)
proj-prefix-send r s _ r≠s
    with  r ≟ r   | s ≟ r
...     | yes _   | no _    = refl
...     | _       | yes s≡r = ⊥-elim (r≠s (sym s≡r))
...     | no r≠r  | no _    = ⊥-elim (r≠r refl)

proj-prefix-recv :
    ∀ { n : ℕ }
    -> (r s : Fin n)
    -> ∀{ l }
    -> (g' : Global n)
    -> (r≠s : r ≢ s)
    -> project (msgSingle r s r≠s l g') s ≡ recvSingle r l (project g' s)
proj-prefix-recv r s _ r≠s
    with  r ≟ s   | s ≟ s
...     | no _    | yes _   = refl
...     | yes r≡s | _       = ⊥-elim (r≠s r≡s)
...     | _       | no s≠s  = ⊥-elim (s≠s refl)

record _↔_ { n : ℕ } (g : Global n) (c : Configuration n) : Set where
    field
        isProj : ∀(p : Fin n) -> lookup c p ≡ project g p

proj-inv-send :
    ∀ { n : ℕ } { g p q l lt' }
    -> project {n} g p ≡ sendSingle q l lt'
    -> (∃[ p≠q ] ∃[ g' ] g ≡ msgSingle p q p≠q l g' × project g' p ≡ lt')
        ⊎ (∃[ r ] ∃[ s ] ∃[ r≠s ] ∃[ l' ] ∃[ g' ]
            g ≡ msgSingle r s r≠s l' g' ×
            r ≢ p ×
            s ≢ p ×
            project g' p ≡ sendSingle q l lt')
proj-inv-send {g = g@endG} projSend = ⊥-elim (endL≢sendSingle projSend)
proj-inv-send {n} {g = g@(msgSingle r s r≠s l' g')} {p} {q} {l} {lt'} projSend
    with r ≟ p   | s ≟ p
...    | yes r≡p | yes s≡p = ⊥-elim (r≠s (trans r≡p (sym s≡p)))
...    | no r≢p  | no s≢p  = inj₂ (r , (s , (r≠s , (l' , (g' , (refl , (r≢p , s≢p , projSend)))))))
...    | yes r≡p | no s≢p  with sendSingle-injective projSend
...                           | s≡q , l'≡l , proj-g'≡lt' = inj₁ (p≠q , (g' , (msgSingle-same , proj-g'≡lt')))
        where
            p≠q : p ≢ q
            p≠q = ≢-subst-right (≢-subst-left r≠s r≡p) s≡q
            msgSingle-same : msgSingle r s r≠s l' g' ≡ msgSingle p q p≠q l g'
            msgSingle-same
                = begin
                    msgSingle r s r≠s l' g'
                ≡⟨ msgSingle-subst-left refl r≡p ⟩
                    msgSingle p s (≢-subst-left r≠s r≡p) l' g'
                ≡⟨ msgSingle-subst-right refl s≡q ⟩
                    msgSingle p q p≠q l' g'
                ≡⟨ cong (λ l -> msgSingle p q p≠q l g') l'≡l ⟩
                    msgSingle p q p≠q l g'
                ∎

proj-inv-recv :
    ∀ { n : ℕ } { g p q l lt' }
    -> project {n} g p ≡ recvSingle q l lt'
    -> (∃[ p≠q ] ∃[ g' ] g ≡ msgSingle q p p≠q l g' × project g' p ≡ lt')
        ⊎ (∃[ r ] ∃[ s ] ∃[ r≠s ] ∃[ l' ] ∃[ g' ]
            g ≡ msgSingle r s r≠s l' g' ×
            r ≢ p ×
            s ≢ p ×
            project g' p ≡ recvSingle q l lt')
proj-inv-recv {g = g@endG} projRecv = ⊥-elim (endL≢recvSingle projRecv)
proj-inv-recv {n} {g = g@(msgSingle r s r≠s l' g')} {p} {q} {l} {lt'} projRecv
    with r ≟ p   | s ≟ p
...    | yes r≡p | yes s≡p = ⊥-elim (r≠s (trans r≡p (sym s≡p)))
...    | no r≢p  | no s≢p  = inj₂ (r , (s , (r≠s , (l' , (g' , (refl , (r≢p , s≢p , projRecv)))))))
...    | no r≢p  | yes s≡p with recvSingle-injective projRecv
...                           | r≡q , l'≡l , proj-g'≡lt' = inj₁ (q≠p , (g' , (msgSingle-same , proj-g'≡lt')))
        where
            q≠p : q ≢ p
            q≠p = ≢-subst-left (≢-subst-right r≠s s≡p) r≡q
            msgSingle-same : msgSingle r s r≠s l' g' ≡ msgSingle q p q≠p l g'
            msgSingle-same
                = begin
                    msgSingle r s r≠s l' g'
                ≡⟨ msgSingle-subst-right refl s≡p ⟩
                    msgSingle r p (≢-subst-right r≠s s≡p) l' g'
                ≡⟨ msgSingle-subst-left refl r≡q ⟩
                    msgSingle q p q≠p l' g'
                ≡⟨ cong (λ l -> msgSingle q p q≠p l g') l'≡l ⟩
                    msgSingle q p q≠p l g'
                ∎

proj-inv-send-recv :
    ∀ { n : ℕ } { g p q l ltp' ltq' }
    -> project {n} g p ≡ sendSingle q l ltp'
    -> project {n} g q ≡ recvSingle p l ltq'
    -> (∃[ p≠q ] ∃[ g' ] g ≡ msgSingle p q p≠q l g' × project g' p ≡ ltp' × project g' q ≡ ltq')
        ⊎ (∃[ r ] ∃[ s ] ∃[ r≠s ] ∃[ l' ] ∃[ g' ]
            g ≡ msgSingle r s r≠s l' g' ×
            r ≢ p ×
            s ≢ p ×
            r ≢ q ×
            s ≢ q ×
            project g' p ≡ sendSingle q l ltp' ×
            project g' q ≡ recvSingle p l ltq')
proj-inv-send-recv {n} {g} {p} {q} {l} {ltp'} {ltq'} projSend projRecv
    with proj-inv-send {n} {g} projSend | proj-inv-recv {n} {g} projRecv
... | inj₁ (p≢q₁ , g₁' , g≡p→q , proj-g₁-p)
    | inj₁ (_ , g₂' , g≡p→q' , proj-g₂-q)
        with msgSingle-injective (trans (sym g≡p→q) g≡p→q')
... | refl , refl , refl , refl
        = inj₁ (p≢q₁ , g₁' , g≡p→q , proj-g₁-p , proj-g₂-q)
proj-inv-send-recv {n} {g} {p} {q} {l} {ltp'} {ltq'} projSend projRecv
    | inj₁ (_ , _ , g≡p→q , _)
    | inj₂ (_ , s , _ , _ , _ , g≡r→s , _ , s≠q , _)
        with msgSingle-injective (trans (sym g≡p→q) g≡r→s)
... | refl , refl , refl , refl = ⊥-elim (s≠q refl)
proj-inv-send-recv {n} {g} {p} {q} {l} {ltp'} {ltq'} projSend projRecv
    | inj₂ (r , _ , _ , _ , _ , g≡r→s , r≠p , _ , _)
    | inj₁ (_ , _ , g≡p→q , _)
        with msgSingle-injective (trans (sym g≡p→q) g≡r→s)
... | refl , refl , refl , refl = ⊥-elim (r≠p refl)
proj-inv-send-recv {n} {g} {p} {q} {l} {ltp'} {ltq'} projSend projRecv
    | inj₂ (r , s , r≠s , l' , g₁' , g≡r→s , r≠p , s≠p , proj-g₁-p)
    | inj₂ (_ , _ , _   , _  , g₂' , g≡r→s' , r≠q , s≠q , proj-g₂-q)
        with msgSingle-injective (trans (sym g≡r→s) g≡r→s')
... | refl , refl , refl , refl
        = inj₂ (r , s , r≠s , l' , g₁' , g≡r→s , r≠p , s≠p , r≠q , s≠q , proj-g₁-p , proj-g₂-q)

config-gt-remove-prefix :
    ∀ { n : ℕ } { p q l p≠q g' }
    -> (g : Global n)
    -> (c : Configuration n)
    -> g ↔ c
    -> (g ≡ msgSingle p q p≠q l g')
    -> ∃[ c' ] ((c' ≡ ((c [ p ]≔ (project g' p)) [ q ]≔ (project g' q))) × (g' ↔ c'))
config-gt-remove-prefix {n} {p} {q} {_} {p≠q} {g'} g c assoc refl = c' , refl , (record { isProj = isProj-g' })
    where
        c' = (c [ p ]≔ (project g' p)) [ q ]≔  (project g' q)
        isProj-g' : ∀ (r : Fin n) -> lookup c' r ≡ project g' r
        isProj-g' r
            with p ≟ r   | q ≟ r
        ...    | yes p≡r | yes q≡r = ⊥-elim (p≠q (trans p≡r (sym q≡r)))
        ...    | yes p≡r | no  _   rewrite (sym p≡r)
                                   rewrite lookup∘update′ p≠q (c [ p ]≔ (project g' p)) (project g' q)
                                   rewrite lookup∘update p c (project g' p)
                                   = refl
        ...    | no _    | yes q≡r rewrite (sym q≡r)
                                   rewrite lookup∘update q (c [ p ]≔ (project g' p)) (project g' q)
                                   = refl
        ...    | no p≠r  | no  q≠r rewrite lookup∘update′ (¬≡-flip q≠r) (c [ p ]≔ (project g' p)) (project g' q)
                                   rewrite lookup∘update′ (¬≡-flip p≠r) c   (project g' p)
                                   rewrite _↔_.isProj assoc r
                                   = proj-prefix-other p q r g' p≠r q≠r
