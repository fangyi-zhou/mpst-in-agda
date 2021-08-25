open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Product using (∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (lookup)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; _≡_; refl; cong; _≢_; module ≡-Reasoning)
open import Data.Product using (∃-syntax; _,_; proj₁; proj₂; _×_)
open ≡-Reasoning

open import Common using (Label; Action; action)
open import Global using (Global; _-_→g_; endG; msgSingle; →g-prefix; →g-cont)
open import Local using (Local; sendSingle; recvSingle; endL; Configuration; _-_→c_; →c-comm; _-_→l_; →l-send; →l-recv; endL≢sendSingle)

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
    ∀ { n : ℕ } { g p q l lt' p≠q }
    -> project {n} g p ≡ sendSingle q l lt'
    -> (∃[ g' ] g ≡ msgSingle p q p≠q l g' × project g' p ≡ lt')
        ⊎ (∃[ r ] ∃[ s ] ∃[ r≠s ] ∃[ l' ] ∃[ g' ]
            g ≡ msgSingle r s r≠s l' g' × r ≢ p × s ≢ p × project g' p ≡ sendSingle q l lt')
proj-inv-send {n} {g = g@endG} {p} {q} projSend = ⊥-elim (endL≢sendSingle projSend)
proj-inv-send {n} {g = g@(msgSingle r s r≠s l' g')} {p} {q} {p≠q = p≠q} projSend
    with r ≟ p   | s ≟ p
...    | yes r≡p | yes s≡p = ⊥-elim (r≠s (trans r≡p (sym s≡p)))
...    | no r≢p  | no s≢p  = inj₂ (r , (s , (r≠s , (l' , (g' , (refl , (r≢p , s≢p , {!   !})))))))
...    | yes r≡p | no _    = inj₁ (g' , ({!   !} , {!   !}))
