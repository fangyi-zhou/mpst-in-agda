open import Common
open import Global

open import Data.Fin
open import Data.Product
open import Data.Sum
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

n = 4

Role = Fin n

p : Role
p = zero

q : Role
q = suc zero

r : Role
r = suc (suc zero)

s : Role
s = suc (suc (suc zero))

l : Label
l = 0

l′ : Label
l′ = 1

g₁ : Global n 0
g₁ = msgSingle′ p q l endG

g₂ : Global n 0
g₂ = recG (msgSingle′ p q l (varG zero)) msg

{-
g₃ : Global n 0
g₃ = recG (varG zero) (guardedVarG {!   !})
-}

g₄ : Global n 0
g₄ = recG (recG (msgSingle′ p q l (varG zero)) msg) guardedRecG

g₄′ : Global n 0
g₄′ = recG (recG (msgSingle′ p q l (varG (suc zero))) msg) guardedRecG

{-
--Untypeable due to unguarded
g₅ : Global n 0
g₅ = msgSingle′ p q l (recG (varG zero) (guardedVarG {!   !}))
-}