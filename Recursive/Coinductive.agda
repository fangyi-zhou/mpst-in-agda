{-# OPTIONS --guardedness #-}

module Recursive.Coinductive where

open import Data.Fin using (Fin; zero) renaming (suc to fsuc)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Recursive.Base

mutual
  record CoGlobal (n : ℕ) (ℓ : ℕ) : Set where
    coinductive
    field
      observeG : CoGlobalView n ℓ

  data CoGlobalView (n : ℕ) (ℓ : ℕ) : Set where
    endCG : CoGlobalView n ℓ
    msgSingleCG : (p q : Fin n) -> p ≢ q -> Fin ℓ -> CoGlobal n ℓ -> CoGlobalView n ℓ

open CoGlobal public

mutual
  record CoLocal (n : ℕ) (ℓ : ℕ) : Set where
    coinductive
    field
      observeL : CoLocalView n ℓ

  data CoLocalView (n : ℕ) (ℓ : ℕ) : Set where
    endCL : CoLocalView n ℓ
    sendSingleCL recvSingleCL : Fin n -> Fin ℓ -> CoLocal n ℓ -> CoLocalView n ℓ

open CoLocal public

private
  variable
    n ℓ Γ : ℕ

EnvG : ℕ -> ℕ -> ℕ -> Set
EnvG n ℓ Γ = Fin Γ -> CoGlobal n ℓ

EnvL : ℕ -> ℕ -> ℕ -> Set
EnvL n ℓ Γ = Fin Γ -> CoLocal n ℓ

extendG : CoGlobal n ℓ -> EnvG n ℓ Γ -> EnvG n ℓ (suc Γ)
extendG g ρ zero = g
extendG g ρ (fsuc x) = ρ x

extendL : CoLocal n ℓ -> EnvL n ℓ Γ -> EnvL n ℓ (suc Γ)
extendL l ρ zero = l
extendL l ρ (fsuc x) = ρ x

emptyEnvG : EnvG n ℓ 0
emptyEnvG ()

emptyEnvL : EnvL n ℓ 0
emptyEnvL ()

coEndG : CoGlobal n ℓ
coEndG .observeG = endCG

coEndL : CoLocal n ℓ
coEndL .observeL = endCL

mutual
  interpRG : (g : RGlobal n ℓ Γ) -> GuardedRG g -> EnvG n ℓ Γ -> CoGlobal n ℓ
  interpRG endRG guarded-endRG ρ .observeG = endCG
  interpRG (msgSingleRG p q p≢q l g) (guarded-msgSingleRG guarded-g) ρ .observeG =
    msgSingleCG p q p≢q l (interpWeakRG g guarded-g ρ)
  interpRG (muRG g) (guarded-muRG guarded-g) ρ = interpMuRG g guarded-g ρ

  {-# TERMINATING #-}
  interpMuRG : (g : RGlobal n ℓ (suc Γ)) -> GuardedBodyRG g -> EnvG n ℓ Γ -> CoGlobal n ℓ
  interpMuRG g guarded-g ρ .observeG =
    interpBodyRG g guarded-g (extendG (interpMuRG g guarded-g ρ) ρ)

  interpBodyRG : (g : RGlobal n ℓ (suc Γ)) -> GuardedBodyRG g -> EnvG n ℓ (suc Γ) -> CoGlobalView n ℓ
  interpBodyRG endRG guarded-body-endRG ρ = endCG
  interpBodyRG (msgSingleRG p q p≢q l g) (guarded-body-msgSingleRG guarded-g) ρ =
    msgSingleCG p q p≢q l (interpWeakRG g guarded-g ρ)

  interpWeakRG : (g : RGlobal n ℓ Γ) -> WeaklyGuardedRG g -> EnvG n ℓ Γ -> CoGlobal n ℓ
  interpWeakRG endRG weak-endRG ρ .observeG = endCG
  interpWeakRG (varRG x) (weak-varRG .x) ρ = ρ x
  interpWeakRG (msgSingleRG p q p≢q l g) (weak-msgSingleRG guarded-g) ρ .observeG =
    msgSingleCG p q p≢q l (interpWeakRG g guarded-g ρ)
  interpWeakRG (muRG g) (weak-muRG guarded-g) ρ = interpMuRG g guarded-g ρ

mutual
  interpRL : (l : RLocal n ℓ Γ) -> GuardedRL l -> EnvL n ℓ Γ -> CoLocal n ℓ
  interpRL endRL guarded-endRL ρ .observeL = endCL
  interpRL (sendSingleRL p l lSub) (guarded-sendSingleRL guarded-lSub) ρ .observeL =
    sendSingleCL p l (interpWeakRL lSub guarded-lSub ρ)
  interpRL (recvSingleRL p l lSub) (guarded-recvSingleRL guarded-lSub) ρ .observeL =
    recvSingleCL p l (interpWeakRL lSub guarded-lSub ρ)
  interpRL (muRL l) (guarded-muRL guarded-l) ρ = interpMuRL l guarded-l ρ

  {-# TERMINATING #-}
  interpMuRL : (l : RLocal n ℓ (suc Γ)) -> GuardedBodyRL l -> EnvL n ℓ Γ -> CoLocal n ℓ
  interpMuRL l guarded-l ρ .observeL =
    interpBodyRL l guarded-l (extendL (interpMuRL l guarded-l ρ) ρ)

  interpBodyRL : (l : RLocal n ℓ (suc Γ)) -> GuardedBodyRL l -> EnvL n ℓ (suc Γ) -> CoLocalView n ℓ
  interpBodyRL endRL guarded-body-endRL ρ = endCL
  interpBodyRL (sendSingleRL p l lSub) (guarded-body-sendSingleRL guarded-lSub) ρ =
    sendSingleCL p l (interpWeakRL lSub guarded-lSub ρ)
  interpBodyRL (recvSingleRL p l lSub) (guarded-body-recvSingleRL guarded-lSub) ρ =
    recvSingleCL p l (interpWeakRL lSub guarded-lSub ρ)

  interpWeakRL : (l : RLocal n ℓ Γ) -> WeaklyGuardedRL l -> EnvL n ℓ Γ -> CoLocal n ℓ
  interpWeakRL endRL weak-endRL ρ .observeL = endCL
  interpWeakRL (varRL x) (weak-varRL .x) ρ = ρ x
  interpWeakRL (sendSingleRL p l lSub) (weak-sendSingleRL guarded-lSub) ρ .observeL =
    sendSingleCL p l (interpWeakRL lSub guarded-lSub ρ)
  interpWeakRL (recvSingleRL p l lSub) (weak-recvSingleRL guarded-lSub) ρ .observeL =
    recvSingleCL p l (interpWeakRL lSub guarded-lSub ρ)
  interpWeakRL (muRL l) (weak-muRL guarded-l) ρ = interpMuRL l guarded-l ρ

regularGlobal : (g : ClosedRGlobal n ℓ) -> GuardedRG g -> CoGlobal n ℓ
regularGlobal g guarded-g = interpRG g guarded-g emptyEnvG

regularLocal : (l : ClosedRLocal n ℓ) -> GuardedRL l -> CoLocal n ℓ
regularLocal l guarded-l = interpRL l guarded-l emptyEnvL
