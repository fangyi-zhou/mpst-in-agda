open import Common
open import Global
open import Projection
open import Local

open import Data.Fin
open import Data.Vec
open import Relation.Binary.PropositionalEquality

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

l' : Label
l' = 1

g₁ : Global n
g₁ = MsgSingle p q (λ ()) l End

lp : Local n
lp = Send q l End

g₁-proj-p-is-lp : project g₁ p ≡ lp
g₁-proj-p-is-lp = refl

lq : Local n
lq = Recv p l End

g₁-proj-q-is-lq : project g₁ q ≡ lq
g₁-proj-q-is-lq = refl

p→q : Action n
p→q = AMsg p q (λ ()) l

r→s : Action n
r→s = AMsg r s (λ ()) l'

g₂ : Global n
g₂ = MsgSingle r s (λ ()) l' g₁

g₂' : Global n
g₂' = MsgSingle r s (λ ()) l' End

g₁→end : g₁ - p→q →g End
g₁→end = GPrefix

g₂→g₁ : g₂ - r→s →g g₁
g₂→g₁ = GPrefix

g₂→g₂' : g₂ - p→q →g g₂'
g₂→g₂' = GCont g₁→end (λ ()) (λ ()) (λ ()) (λ ())

g₁-proj-p→end : (project g₁ p) - p→q →l End
g₁-proj-p→end = LSend p λ ()

g₁-proj-q→end : (project g₁ q) - p→q →l End
g₁-proj-q→end = LRecv q λ ()

g₂-proj-p→g₂'-proj-p : (project g₂ p) - p→q →l (project g₂' p)
g₂-proj-p→g₂'-proj-p = LSend p λ ()

g₂-proj-q→g₂'-proj-q : (project g₂ q) - p→q →l (project g₂' q)
g₂-proj-q→g₂'-proj-q = LRecv q λ ()

c₁ : Configuration n
c₁ = lp ∷ lq ∷ End ∷ End ∷ []

cEnd : Configuration n
cEnd = End ∷ End ∷ End ∷ End ∷ []

c₁→cEnd : c₁ - p→q →c cEnd
c₁→cEnd = CComm c₁ (λ ()) g₁-proj-p→end g₁-proj-q→end

g₁↔c₁ : g₁ ↔ c₁
g₁↔c₁ = record { isProj = refls }
  where
    refls : (p : Fin n) -> lookup c₁ p ≡ project g₁ p
    refls zero = refl
    refls (suc zero) = refl
    refls (suc (suc zero)) = refl
    refls (suc (suc (suc zero))) = refl
