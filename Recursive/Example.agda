{-# OPTIONS --guardedness #-}

module Recursive.Example where

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Common
open import Recursive.Base
open import Recursive.Coinductive
open import Recursive.Operational
open import Recursive.Projection

n : ℕ
n = 2

ℓ : ℕ
ℓ = 1

Role : Set
Role = Fin n

Label : Set
Label = Fin ℓ

p q : Role
p = zero
q = suc zero

p≢q : p ≢ q
p≢q ()

label : Label
label = zero

p→q : Action n ℓ
p→q = action p q p≢q label

loopRG : ClosedRGlobal n ℓ
loopRG = muRG (msgSingleRG p q p≢q label (varRG zero))

loopRG-guarded : GuardedRG loopRG
loopRG-guarded = guarded-muRG (guarded-body-msgSingleRG (weak-varRG zero))

loopCG : CoGlobal n ℓ
loopCG .observeG = msgSingleCG p q p≢q label loopCG

loopRG-regular : RegularGlobal loopRG loopCG
stepRG loopRG-regular = step-muRG (body-msgSingleRG loopRG-cont)
  where
    loopRG-cont : InterpWeakRG (extendG loopCG emptyEnvG) (varRG zero) loopCG
    weakStepRG loopRG-cont = weak-varRG (refl≈CG loopCG)

loopRG→loopRG : loopRG - p→q →rg loopRG
loopRG→loopRG = →rg-unfold →rg-prefix

loopCG→loopCG : loopCG - p→q →cg loopCG
loopCG→loopCG = →cg-prefix refl

loopRL-p : ClosedRLocal n ℓ
loopRL-p = projectR loopRG p

loopRL-q : ClosedRLocal n ℓ
loopRL-q = projectR loopRG q

loopCL-p : CoLocal n ℓ
loopCL-p .observeL = sendSingleCL q label loopCL-p

loopCL-q : CoLocal n ℓ
loopCL-q .observeL = recvSingleCL p label loopCL-q

loopRL-p-regular : RegularLocal loopRL-p loopCL-p
stepRL loopRL-p-regular = step-muRL (body-sendSingleRL loopRL-p-cont)
  where
    loopRL-p-cont : InterpWeakRL (extendL loopCL-p emptyEnvL) (varRL zero) loopCL-p
    weakStepRL loopRL-p-cont = weak-varRL (refl≈CL loopCL-p)

loopRL-q-regular : RegularLocal loopRL-q loopCL-q
stepRL loopRL-q-regular = step-muRL (body-recvSingleRL loopRL-q-cont)
  where
    loopRL-q-cont : InterpWeakRL (extendL loopCL-q emptyEnvL) (varRL zero) loopCL-q
    weakStepRL loopRL-q-cont = weak-varRL (refl≈CL loopCL-q)

loopRL-p→loopRL-p : (p , loopRL-p) - p→q →rl (p , loopRL-p)
loopRL-p→loopRL-p = →rl-unfold (→rl-send refl)

loopRL-q→loopRL-q : (q , loopRL-q) - p→q →rl (q , loopRL-q)
loopRL-q→loopRL-q = →rl-unfold (→rl-recv refl)
