module Recursive.Base where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero) renaming (suc to fsuc)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Common

data RGlobal (n : ℕ) (ℓ : ℕ) (Γ : ℕ) : Set where
  endRG : RGlobal n ℓ Γ
  varRG : Fin Γ -> RGlobal n ℓ Γ
  muRG : RGlobal n ℓ (suc Γ) -> RGlobal n ℓ Γ
  msgSingleRG : (p q : Fin n) -> p ≢ q -> Fin ℓ -> RGlobal n ℓ Γ -> RGlobal n ℓ Γ

data RLocal (n : ℕ) (ℓ : ℕ) (Γ : ℕ) : Set where
  endRL : RLocal n ℓ Γ
  varRL : Fin Γ -> RLocal n ℓ Γ
  muRL : RLocal n ℓ (suc Γ) -> RLocal n ℓ Γ
  sendSingleRL recvSingleRL : Fin n -> Fin ℓ -> RLocal n ℓ Γ -> RLocal n ℓ Γ

ClosedRGlobal : ℕ -> ℕ -> Set
ClosedRGlobal n ℓ = RGlobal n ℓ 0

ClosedRLocal : ℕ -> ℕ -> Set
ClosedRLocal n ℓ = RLocal n ℓ 0

private
  variable
    n ℓ Γ Δ : ℕ

renameRG : (Fin Γ -> Fin Δ) -> RGlobal n ℓ Γ -> RGlobal n ℓ Δ
renameRG ρ endRG = endRG
renameRG ρ (varRG x) = varRG (ρ x)
renameRG {Γ = Γ} {Δ = Δ} ρ (muRG g) = muRG (renameRG ρ′ g)
  where
    ρ′ : Fin (suc Γ) -> Fin (suc Δ)
    ρ′ zero = zero
    ρ′ (fsuc x) = fsuc (ρ x)
renameRG ρ (msgSingleRG p q p≢q l g) = msgSingleRG p q p≢q l (renameRG ρ g)

renameRL : (Fin Γ -> Fin Δ) -> RLocal n ℓ Γ -> RLocal n ℓ Δ
renameRL ρ endRL = endRL
renameRL ρ (varRL x) = varRL (ρ x)
renameRL {Γ = Γ} {Δ = Δ} ρ (muRL l) = muRL (renameRL ρ′ l)
  where
    ρ′ : Fin (suc Γ) -> Fin (suc Δ)
    ρ′ zero = zero
    ρ′ (fsuc x) = fsuc (ρ x)
renameRL ρ (sendSingleRL p l lSub) = sendSingleRL p l (renameRL ρ lSub)
renameRL ρ (recvSingleRL p l lSub) = recvSingleRL p l (renameRL ρ lSub)

SubRG : ℕ -> ℕ -> ℕ -> ℕ -> Set
SubRG n ℓ Γ Δ = Fin Γ -> RGlobal n ℓ Δ

SubRL : ℕ -> ℕ -> ℕ -> ℕ -> Set
SubRL n ℓ Γ Δ = Fin Γ -> RLocal n ℓ Δ

liftRG : SubRG n ℓ Γ Δ -> SubRG n ℓ (suc Γ) (suc Δ)
liftRG σ zero = varRG zero
liftRG σ (fsuc x) = renameRG fsuc (σ x)

liftRL : SubRL n ℓ Γ Δ -> SubRL n ℓ (suc Γ) (suc Δ)
liftRL σ zero = varRL zero
liftRL σ (fsuc x) = renameRL fsuc (σ x)

substRG : RGlobal n ℓ Γ -> SubRG n ℓ Γ Δ -> RGlobal n ℓ Δ
substRG endRG σ = endRG
substRG (varRG x) σ = σ x
substRG (muRG g) σ = muRG (substRG g (liftRG σ))
substRG (msgSingleRG p q p≢q l g) σ = msgSingleRG p q p≢q l (substRG g σ)

substRL : RLocal n ℓ Γ -> SubRL n ℓ Γ Δ -> RLocal n ℓ Δ
substRL endRL σ = endRL
substRL (varRL x) σ = σ x
substRL (muRL l) σ = muRL (substRL l (liftRL σ))
substRL (sendSingleRL p l lSub) σ = sendSingleRL p l (substRL lSub σ)
substRL (recvSingleRL p l lSub) σ = recvSingleRL p l (substRL lSub σ)

unfoldRG : RGlobal n ℓ Γ -> RGlobal n ℓ Γ
unfoldRG endRG = endRG
unfoldRG (varRG x) = varRG x
unfoldRG (msgSingleRG p q p≢q l g) = msgSingleRG p q p≢q l g
unfoldRG {n = n} {ℓ = ℓ} {Γ = Γ} (muRG g) = substRG g σ
  where
    σ : SubRG n ℓ (suc Γ) Γ
    σ zero = muRG g
    σ (fsuc x) = varRG x

unfoldRL : RLocal n ℓ Γ -> RLocal n ℓ Γ
unfoldRL endRL = endRL
unfoldRL (varRL x) = varRL x
unfoldRL (sendSingleRL p l lSub) = sendSingleRL p l lSub
unfoldRL (recvSingleRL p l lSub) = recvSingleRL p l lSub
unfoldRL {n = n} {ℓ = ℓ} {Γ = Γ} (muRL l) = substRL l σ
  where
    σ : SubRL n ℓ (suc Γ) Γ
    σ zero = muRL l
    σ (fsuc x) = varRL x

mutual
  data GuardedRG {n ℓ Γ : ℕ} : RGlobal n ℓ Γ -> Set where
    guarded-endRG : GuardedRG endRG
    guarded-msgSingleRG :
      ∀ {p q p≢q l g}
      -> WeaklyGuardedRG g
      -> GuardedRG (msgSingleRG p q p≢q l g)
    guarded-muRG :
      ∀ {g}
      -> GuardedBodyRG g
      -> GuardedRG (muRG g)

  data GuardedBodyRG {n ℓ Γ : ℕ} : RGlobal n ℓ (suc Γ) -> Set where
    guarded-body-endRG : GuardedBodyRG endRG
    guarded-body-msgSingleRG :
      ∀ {p q p≢q l g}
      -> WeaklyGuardedRG g
      -> GuardedBodyRG (msgSingleRG p q p≢q l g)

  data WeaklyGuardedRG {n ℓ Γ : ℕ} : RGlobal n ℓ Γ -> Set where
    weak-endRG : WeaklyGuardedRG endRG
    weak-varRG : ∀ x -> WeaklyGuardedRG (varRG x)
    weak-msgSingleRG :
      ∀ {p q p≢q l g}
      -> WeaklyGuardedRG g
      -> WeaklyGuardedRG (msgSingleRG p q p≢q l g)
    weak-muRG :
      ∀ {g}
      -> GuardedBodyRG g
      -> WeaklyGuardedRG (muRG g)

mutual
  data GuardedRL {n ℓ Γ : ℕ} : RLocal n ℓ Γ -> Set where
    guarded-endRL : GuardedRL endRL
    guarded-sendSingleRL :
      ∀ {p l lSub}
      -> WeaklyGuardedRL lSub
      -> GuardedRL (sendSingleRL p l lSub)
    guarded-recvSingleRL :
      ∀ {p l lSub}
      -> WeaklyGuardedRL lSub
      -> GuardedRL (recvSingleRL p l lSub)
    guarded-muRL :
      ∀ {l}
      -> GuardedBodyRL l
      -> GuardedRL (muRL l)

  data GuardedBodyRL {n ℓ Γ : ℕ} : RLocal n ℓ (suc Γ) -> Set where
    guarded-body-endRL : GuardedBodyRL endRL
    guarded-body-sendSingleRL :
      ∀ {p l lSub}
      -> WeaklyGuardedRL lSub
      -> GuardedBodyRL (sendSingleRL p l lSub)
    guarded-body-recvSingleRL :
      ∀ {p l lSub}
      -> WeaklyGuardedRL lSub
      -> GuardedBodyRL (recvSingleRL p l lSub)

  data WeaklyGuardedRL {n ℓ Γ : ℕ} : RLocal n ℓ Γ -> Set where
    weak-endRL : WeaklyGuardedRL endRL
    weak-varRL : ∀ x -> WeaklyGuardedRL (varRL x)
    weak-sendSingleRL :
      ∀ {p l lSub}
      -> WeaklyGuardedRL lSub
      -> WeaklyGuardedRL (sendSingleRL p l lSub)
    weak-recvSingleRL :
      ∀ {p l lSub}
      -> WeaklyGuardedRL lSub
      -> WeaklyGuardedRL (recvSingleRL p l lSub)
    weak-muRL :
      ∀ {l}
      -> GuardedBodyRL l
      -> WeaklyGuardedRL (muRL l)

unguarded-loopRG : ∀ {n ℓ Γ} -> GuardedBodyRG (varRG {n} {ℓ} {suc Γ} zero) -> ⊥
unguarded-loopRG ()

unguarded-loopRL : ∀ {n ℓ Γ} -> GuardedBodyRL (varRL {n} {ℓ} {suc Γ} zero) -> ⊥
unguarded-loopRL ()
