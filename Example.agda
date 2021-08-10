open import Common
open import Global

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

g₁→end : g₁ - (AMsg p q l) →ᵍ End
g₁→end = GPrefix

g₂→g₁ : g₂ - (AMsg r s l') →ᵍ g₁
g₂→g₁ = GPrefix

g₂→g₂' : g₂ - (AMsg p q l) →ᵍ g₂'
g₂→g₂' = GCont g₁→end (λ ()) (λ ()) (λ ()) (λ ())
