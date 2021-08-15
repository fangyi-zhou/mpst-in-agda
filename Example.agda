open import Common
open import Global
open import Projection
open import Local

open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Nat.Properties using (<-strictTotalOrder)
import Data.Tree.AVL <-strictTotalOrder as Map
open Map using (_,_)

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

lp : Local
lp = Send q l End

g₁-proj-p-is-lp : project g₁ p ≡ lp
g₁-proj-p-is-lp = refl

lq : Local
lq = Recv p l End

g₁-proj-q-is-lq : project g₁ q ≡ lq
g₁-proj-q-is-lq = refl

p→q : Action
p→q = AMsg p q (λ ()) l

r→s : Action
r→s = AMsg r s (λ ()) l'

g₂ : Global
g₂ = MsgSingle r s (λ ()) l' g₁

g₂' : Global
g₂' = MsgSingle r s (λ ()) l' End

g₁→end : g₁ - p→q →g End
g₁→end = GPrefix

g₂→g₁ : g₂ - r→s →g g₁
g₂→g₁ = GPrefix

g₂→g₂' : g₂ - p→q →g g₂'
g₂→g₂' = GCont g₁→end (λ ()) (λ ()) (λ ()) (λ ())

g₁-proj-p→end : (p , project g₁ p) - p→q →l (p , End)
g₁-proj-p→end = LSend

g₁-proj-q→end : (q , project g₁ q) - p→q →l (q , End)
g₁-proj-q→end = LRecv

g₂-proj-p→g₂'-proj-p : (p , project g₂ p) - p→q →l (p , project g₂' p)
g₂-proj-p→g₂'-proj-p = LSend

g₂-proj-q→g₂'-proj-q : (q , project g₂ q) - p→q →l (q , project g₂' q)
g₂-proj-q→g₂'-proj-q = LRecv

c₁ : Configuration
c₁ = Map.fromList ((p , project g₁ p) ∷ (q , project g₁ q) ∷ [])

cEnd : Configuration
cEnd = Map.fromList ((p , End) ∷ (q , End) ∷ [])

c₁→cEnd : c₁ - p→q →c cEnd
c₁→cEnd = CComm c₁ (λ ()) refl refl LSend LRecv
