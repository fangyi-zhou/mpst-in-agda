module Recursive.Projection where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; _≟_)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)
open import Relation.Nullary using (yes; no)

open import Recursive.Base

private
  variable
    n ℓ Γ : ℕ

projectR : RGlobal n ℓ Γ -> Fin n -> RLocal n ℓ Γ
projectR endRG p = endRL
projectR (varRG x) p = varRL x
projectR (muRG g) p = muRL (projectR g p)
projectR (msgSingleRG p q p≢q l g) r
  with p ≟ r | q ≟ r
... | yes _    | no _     = sendSingleRL q l (projectR g r)
... | no _     | yes _    = recvSingleRL p l (projectR g r)
... | no _     | no _     = projectR g r
... | yes p≡r | yes q≡r = ⊥-elim (p≢q (trans p≡r (sym q≡r)))

RConfiguration : ℕ -> ℕ -> ℕ -> Set
RConfiguration n ℓ Γ = Vec (RLocal n ℓ Γ) n

record _↔r_ {n ℓ Γ : ℕ} (g : RGlobal n ℓ Γ) (c : RConfiguration n ℓ Γ) : Set where
  field
    isProjR : ∀ (p : Fin n) -> lookup c p ≡ projectR g p

open _↔r_ public
