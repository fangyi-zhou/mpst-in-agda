{-# OPTIONS --guardedness #-}

module Recursive.Coinductive where

open import Data.Fin using (Fin; zero) renaming (suc to fsuc)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

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
  record _≈CG_ {n ℓ : ℕ} (g h : CoGlobal n ℓ) : Set where
    coinductive
    field
      view≈G : CoGlobalView≈ (observeG g) (observeG h)

  data CoGlobalView≈ {n ℓ : ℕ} : CoGlobalView n ℓ -> CoGlobalView n ℓ -> Set where
    end≈CG : CoGlobalView≈ endCG endCG
    msgSingle≈CG :
      ∀ {p q p≢q p≢q′ l g h}
      -> g ≈CG h
      -> CoGlobalView≈ (msgSingleCG p q p≢q l g) (msgSingleCG p q p≢q′ l h)

open _≈CG_ public

refl≈CG : (g : CoGlobal n ℓ) -> g ≈CG g
view≈G (refl≈CG g) with observeG g
... | endCG = end≈CG
... | msgSingleCG p q p≢q l gSub = msgSingle≈CG (refl≈CG gSub)

mutual
  record InterpRG {n ℓ Γ : ℕ} (ρ : EnvG n ℓ Γ) (g : RGlobal n ℓ Γ) (cg : CoGlobal n ℓ) : Set where
    coinductive
    field
      stepRG : StepRG ρ g (observeG cg)

  data StepRG {n ℓ Γ : ℕ} (ρ : EnvG n ℓ Γ) : RGlobal n ℓ Γ -> CoGlobalView n ℓ -> Set where
    step-endRG : StepRG ρ endRG endCG
    step-msgSingleRG :
      ∀ {p q p≢q l g cg}
      -> InterpWeakRG ρ g cg
      -> StepRG ρ (msgSingleRG p q p≢q l g) (msgSingleCG p q p≢q l cg)
    step-muRG :
      ∀ {g cg}
      -> BodyStepRG (extendG cg ρ) g (observeG cg)
      -> StepRG ρ (muRG g) (observeG cg)

  data BodyStepRG {n ℓ Γ : ℕ} (ρ : EnvG n ℓ Γ) : RGlobal n ℓ Γ -> CoGlobalView n ℓ -> Set where
    body-endRG : BodyStepRG ρ endRG endCG
    body-msgSingleRG :
      ∀ {p q p≢q l g cg}
      -> InterpWeakRG ρ g cg
      -> BodyStepRG ρ (msgSingleRG p q p≢q l g) (msgSingleCG p q p≢q l cg)

  record InterpWeakRG {n ℓ Γ : ℕ} (ρ : EnvG n ℓ Γ) (g : RGlobal n ℓ Γ) (cg : CoGlobal n ℓ) : Set where
    coinductive
    field
      weakStepRG : WeakStepRG ρ g cg

  data WeakStepRG {n ℓ Γ : ℕ} (ρ : EnvG n ℓ Γ) : RGlobal n ℓ Γ -> CoGlobal n ℓ -> Set where
    weak-endRG :
      ∀ {cg}
      -> observeG cg ≡ endCG
      -> WeakStepRG ρ endRG cg
    weak-varRG :
      ∀ {x cg}
      -> cg ≈CG ρ x
      -> WeakStepRG ρ (varRG x) cg
    weak-msgSingleRG :
      ∀ {p q p≢q l g cg cgSub}
      -> observeG cg ≡ msgSingleCG p q p≢q l cgSub
      -> InterpWeakRG ρ g cgSub
      -> WeakStepRG ρ (msgSingleRG p q p≢q l g) cg
    weak-muRG :
      ∀ {g cg}
      -> InterpRG ρ (muRG g) cg
      -> WeakStepRG ρ (muRG g) cg

open InterpRG public
open InterpWeakRG public

RegularGlobal : ClosedRGlobal n ℓ -> CoGlobal n ℓ -> Set
RegularGlobal = InterpRG emptyEnvG

mutual
  record _≈CL_ {n ℓ : ℕ} (l m : CoLocal n ℓ) : Set where
    coinductive
    field
      view≈L : CoLocalView≈ (observeL l) (observeL m)

  data CoLocalView≈ {n ℓ : ℕ} : CoLocalView n ℓ -> CoLocalView n ℓ -> Set where
    end≈CL : CoLocalView≈ endCL endCL
    sendSingle≈CL :
      ∀ {p l c d}
      -> c ≈CL d
      -> CoLocalView≈ (sendSingleCL p l c) (sendSingleCL p l d)
    recvSingle≈CL :
      ∀ {p l c d}
      -> c ≈CL d
      -> CoLocalView≈ (recvSingleCL p l c) (recvSingleCL p l d)

open _≈CL_ public

refl≈CL : (l : CoLocal n ℓ) -> l ≈CL l
view≈L (refl≈CL l) with observeL l
... | endCL = end≈CL
... | sendSingleCL p label lSub = sendSingle≈CL (refl≈CL lSub)
... | recvSingleCL p label lSub = recvSingle≈CL (refl≈CL lSub)

mutual
  record InterpRL {n ℓ Γ : ℕ} (ρ : EnvL n ℓ Γ) (l : RLocal n ℓ Γ) (cl : CoLocal n ℓ) : Set where
    coinductive
    field
      stepRL : StepRL ρ l (observeL cl)

  data StepRL {n ℓ Γ : ℕ} (ρ : EnvL n ℓ Γ) : RLocal n ℓ Γ -> CoLocalView n ℓ -> Set where
    step-endRL : StepRL ρ endRL endCL
    step-sendSingleRL :
      ∀ {p label l cl}
      -> InterpWeakRL ρ l cl
      -> StepRL ρ (sendSingleRL p label l) (sendSingleCL p label cl)
    step-recvSingleRL :
      ∀ {p label l cl}
      -> InterpWeakRL ρ l cl
      -> StepRL ρ (recvSingleRL p label l) (recvSingleCL p label cl)
    step-muRL :
      ∀ {l cl}
      -> BodyStepRL (extendL cl ρ) l (observeL cl)
      -> StepRL ρ (muRL l) (observeL cl)

  data BodyStepRL {n ℓ Γ : ℕ} (ρ : EnvL n ℓ Γ) : RLocal n ℓ Γ -> CoLocalView n ℓ -> Set where
    body-endRL : BodyStepRL ρ endRL endCL
    body-sendSingleRL :
      ∀ {p label l cl}
      -> InterpWeakRL ρ l cl
      -> BodyStepRL ρ (sendSingleRL p label l) (sendSingleCL p label cl)
    body-recvSingleRL :
      ∀ {p label l cl}
      -> InterpWeakRL ρ l cl
      -> BodyStepRL ρ (recvSingleRL p label l) (recvSingleCL p label cl)

  record InterpWeakRL {n ℓ Γ : ℕ} (ρ : EnvL n ℓ Γ) (l : RLocal n ℓ Γ) (cl : CoLocal n ℓ) : Set where
    coinductive
    field
      weakStepRL : WeakStepRL ρ l cl

  data WeakStepRL {n ℓ Γ : ℕ} (ρ : EnvL n ℓ Γ) : RLocal n ℓ Γ -> CoLocal n ℓ -> Set where
    weak-endRL :
      ∀ {cl}
      -> observeL cl ≡ endCL
      -> WeakStepRL ρ endRL cl
    weak-varRL :
      ∀ {x cl}
      -> cl ≈CL ρ x
      -> WeakStepRL ρ (varRL x) cl
    weak-sendSingleRL :
      ∀ {p label l cl clSub}
      -> observeL cl ≡ sendSingleCL p label clSub
      -> InterpWeakRL ρ l clSub
      -> WeakStepRL ρ (sendSingleRL p label l) cl
    weak-recvSingleRL :
      ∀ {p label l cl clSub}
      -> observeL cl ≡ recvSingleCL p label clSub
      -> InterpWeakRL ρ l clSub
      -> WeakStepRL ρ (recvSingleRL p label l) cl
    weak-muRL :
      ∀ {l cl}
      -> InterpRL ρ (muRL l) cl
      -> WeakStepRL ρ (muRL l) cl

open InterpRL public
open InterpWeakRL public

RegularLocal : ClosedRLocal n ℓ -> CoLocal n ℓ -> Set
RegularLocal = InterpRL emptyEnvL
