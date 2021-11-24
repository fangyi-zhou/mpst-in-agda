open import Common
open import Global
open import Projection
open import Local

open import Data.Fin
open import Data.Product
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

l′ : Label
l′ = 1

g₁ : Global n
g₁ = msgSingle′ p q l endG

lp : Local n
lp = sendSingle q l endL

g₁-proj-p-is-lp : project g₁ p ≡ lp
g₁-proj-p-is-lp = refl

lq : Local n
lq = recvSingle p l endL

g₁-proj-q-is-lq : project g₁ q ≡ lq
g₁-proj-q-is-lq = refl

p→q : Action n
p→q = action′ p q l

r→s : Action n
r→s = action′ r s l′

g₂ : Global n
g₂ = msgSingle′ r s l′ g₁

g₂′ : Global n
g₂′ = msgSingle′ r s l′ endG

g₁→end : g₁ - p→q →g endG
g₁→end = →g-prefix

g₂→g₁ : g₂ - r→s →g g₁
g₂→g₁ = →g-prefix

g₂→g₂′ : g₂ - p→q →g g₂′
g₂→g₂′ = →g-cont g₁→end (λ ()) (λ ()) (λ ()) (λ ())

g₁-proj-p→end : (p , project g₁ p) - p→q →l (p , endL)
g₁-proj-p→end = →l-send p refl λ ()

g₁-proj-q→end : (q , project g₁ q) - p→q →l (q , endL)
g₁-proj-q→end = →l-recv q refl λ ()

g₂-proj-p→g₂′-proj-p : (p , project g₂ p) - p→q →l (p , project g₂′ p)
g₂-proj-p→g₂′-proj-p = →l-send p refl λ ()

g₂-proj-q→g₂′-proj-q : (q , project g₂ q) - p→q →l (q , project g₂′ q)
g₂-proj-q→g₂′-proj-q = →l-recv q refl λ ()

c₁ : Configuration n
c₁ = lp ∷ lq ∷ endL ∷ endL ∷ []

cEnd : Configuration n
cEnd = endL ∷ endL ∷ endL ∷ endL ∷ []

c₁→cEnd : c₁ - p→q →c cEnd
c₁→cEnd = →c-comm c₁ (λ ()) refl refl refl g₁-proj-p→end g₁-proj-q→end

g₁↔c₁ : g₁ ↔ c₁
g₁↔c₁ = record { isProj = refls }
  where
    refls : (p : Fin n) -> lookup c₁ p ≡ project g₁ p
    refls zero = refl
    refls (suc zero) = refl
    refls (suc (suc zero)) = refl
    refls (suc (suc (suc zero))) = refl
