open import Common
open import Global

open import Data.Fin
open import Data.Nat
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

g₄ : Global n 0
g₄ = recG (recG (msgSingle′ p q l (varG zero)) msg) (guardedRecG msg)

g₄′ : Global n 0
g₄′ = recG (recG (msgSingle′ p q l (varG (suc zero))) msg) (guardedRecG msg)

{-
--Untypeable due to unguarded
g₅ : Global n 0
g₅ = msgSingle′ p q l (recG (varG zero) (guardedVarG {!   !}))

g₃ : Global n 0
g₃ = recG (varG zero) (guardedVarG {!   !})

gggg : Global n 0
gggg = recG( recG (varG zero) (guardedVarG {!   !})) (guardedRecG (guardedVarG {!   !}))

ggggg : Global n 0
ggggg = recG (recG (varG (suc zero)) (guardedVarG {!   !})) (guardedRecG (guardedVarG {!   !}))
-}

gg : Global n 0
gg = recG (recG (msgSingle′ p q l (varG zero)) msg) (guardedRecG msg)

ggg : Global n 0
ggg = recG (recG (msgSingle′ p q l (varG (suc zero))) msg) (guardedRecG msg)
