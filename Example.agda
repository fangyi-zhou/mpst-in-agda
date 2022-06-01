open import Common
open import Global

open import Data.Fin
open import Data.Product
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
g₂ = muG (msgSingle′ p q l (recG zero))

g₂Guarded : GuardedG 0 g₂
g₂Guarded = rec msg (msg (var zero))

g₃ : Global n 0
g₃ = muG (recG zero)

g₃Unguarded : ¬ (GuardedG 0 g₃)
g₃Unguarded (rec (var .zero x) x₁) = x refl

g₄ : Global n 0
g₄ = muG (muG (msgSingle′ p q l (recG zero)))

g₄Guarded : GuardedG 0 g₄
g₄Guarded = rec (rec msg) (rec msg (msg (var zero)))

g₄′ : Global n 0
g₄′ = muG (muG (msgSingle′ p q l (recG (suc zero))))

g₄′Guarded : GuardedG 0 g₄′
g₄′Guarded = rec (rec msg) (rec msg (msg (var (suc zero))))
