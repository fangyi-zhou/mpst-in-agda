module Participation where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Relation.Nullary using (yes; no)

open import Common
open import Global
open import Local
open import Projection using (project; proj-prefix-send; proj-prefix-recv)

private
  variable
    n ℓ : ℕ
    p : Fin n
    g : Global n ℓ

-- A role p participates in a global type if it appears as sender or
-- receiver in some communication prefix of the global type.
data Participates {n ℓ : ℕ} (p : Fin n) : Global n ℓ → Set where
  here-send : ∀ {q p≢q l gSub} → Participates p (msgSingle p q p≢q l gSub)
  here-recv : ∀ {q q≢p l gSub} → Participates p (msgSingle q p q≢p l gSub)
  there     : ∀ {r s r≢s l gSub} → Participates p gSub → Participates p (msgSingle r s r≢s l gSub)

-- Forward direction: if p participates in g then its projection is not endL.
-- Note: project uses with-abstraction, so we mirror the same case split to
-- force the stuck terms to reduce before matching against endL≢sendSingle /
-- endL≢recvSingle.
participates→proj≢end : Participates p g → project g p ≢ endL
participates→proj≢end {p = p} (here-send {q = q} {p≢q = p≢q} {l = l} {gSub = gSub})
  with p ≟ p | q ≟ p
... | yes refl | yes refl = ⊥-elim (p≢q (sym refl))
... | yes refl | no  _    = λ h → endL≢sendSingle (sym h)
... | no  p≢p  | _        = ⊥-elim (p≢p refl)
participates→proj≢end {p = p} (here-recv {q = q} {q≢p = q≢p} {l = l} {gSub = gSub})
  with q ≟ p | p ≟ p
... | yes q≡p  | _        = ⊥-elim (q≢p q≡p)
... | no  _    | yes refl = λ h → endL≢recvSingle (sym h)
... | no  _    | no  p≢p  = ⊥-elim (p≢p refl)
participates→proj≢end {p = p} (there {r = r} {s = s} {r≢s = r≢s} {l = l} {gSub = gSub} part)
  with r ≟ p | s ≟ p
... | yes refl | yes refl = ⊥-elim (r≢s refl)
... | yes refl | no  _    = λ h → endL≢sendSingle (sym h)
... | no  _    | yes refl = λ h → endL≢recvSingle (sym h)
... | no  r≢p  | no  s≢p  = participates→proj≢end part

-- Backward direction: if the projection of g onto p is not endL then p
-- participates in g.
proj≢end→participates : project g p ≢ endL → Participates p g
proj≢end→participates {g = endG} h = ⊥-elim (h refl)
proj≢end→participates {g = msgSingle r s r≢s l gSub} {p = p} h
  with r ≟ p | s ≟ p
... | yes refl | yes refl = ⊥-elim (r≢s refl)
... | yes refl | no _     = here-send
... | no _     | yes refl = here-recv
... | no r≢p   | no s≢p   = there (proj≢end→participates h)

-- p participates in g if and only if the projection of g onto p is not endL.
participates-iff : Participates p g ⇔ (project g p ≢ endL)
participates-iff = mk⇔ participates→proj≢end proj≢end→participates
