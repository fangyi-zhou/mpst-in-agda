open import Common
open import Global
open import Projection
open import Local

p : Role
p = 0

q : Role
q = 1

r : Role
r = 2

s : Role
s = 3

l : Label
l = 0

l' : Label
l' = 1

g₁ : Global
g₁ = MsgSingle p q (λ ()) l End

g₂ : Global
g₂ = MsgSingle r s (λ ()) l' g₁

g₂' : Global
g₂' = MsgSingle r s (λ ()) l' End

g₁→end : g₁ - (AMsg p q (λ ()) l) →g End
g₁→end = GPrefix

g₂→g₁ : g₂ - (AMsg r s (λ ()) l') →g g₁
g₂→g₁ = GPrefix

g₂→g₂' : g₂ - (AMsg p q (λ ()) l) →g g₂'
g₂→g₂' = GCont g₁→end (λ ()) (λ ()) (λ ()) (λ ())

g₁-proj-p→end : (p , project g₁ p) - (AMsg p q (λ ()) l) →l (p , End)
g₁-proj-p→end = LSend

g₁-proj-q→end : (q , project g₁ q) - (AMsg p q (λ ()) l) →l (q , End)
g₁-proj-q→end = LRecv

g₂-proj-p→g₂'-proj-p : (p , project g₂ p) - (AMsg p q (λ ()) l) →l (p , project g₂' p)
g₂-proj-p→g₂'-proj-p = LSend

g₂-proj-q→g₂'-proj-q : (q , project g₂ q) - (AMsg p q (λ ()) l) →l (q , project g₂' q)
g₂-proj-q→g₂'-proj-q = LRecv
