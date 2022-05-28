open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; lookup; _[_]≔_)

open import Common

data Local (n : ℕ) : Set where
  endL : Local n
  sendSingle recvSingle : Fin n -> Label -> Local n -> Local n

private
  variable
    n : ℕ
    p p′ q : Fin n
    l l′ : Label
    lSub lSub′ : Local n

endL≢sendSingle : ∀ { lSub } -> endL {n} ≢ sendSingle q l lSub
endL≢sendSingle ()

endL≢recvSingle : ∀ { lSub } -> endL {n} ≢ recvSingle q l lSub
endL≢recvSingle ()

sendSingle-injective :
  sendSingle {n} p l lSub ≡ sendSingle p′ l′ lSub′
  -> p ≡ p′ × l ≡ l′ × lSub ≡ lSub′
sendSingle-injective refl = refl , refl , refl

recvSingle-injective :
  recvSingle {n} p l lSub ≡ recvSingle p′ l′ lSub′
  -> p ≡ p′ × l ≡ l′ × lSub ≡ lSub′
recvSingle-injective refl = refl , refl , refl

Configuration : ℕ -> Set
Configuration n = Vec (Local n) n

data _-_→l_ {n : ℕ} : (Fin n × Local n) -> Action n -> (Fin n × Local n) -> Set where
  →l-send :
    ∀ { lp lpSub }
    -> (p : Fin n)
    -> lp ≡ sendSingle q l lpSub
    -> (p≢q : p ≢ q)
    -> (p , lp) - (action p q p≢q l) →l (p , lpSub)
  →l-recv :
    ∀ { lp lpSub }
    -> (p : Fin n)
    -> lp ≡ recvSingle q l lpSub
    -> (q≢p : q ≢ p)
    -> (p , lp) - (action q p q≢p l) →l (p , lpSub)

data _-_→c_ {n : ℕ} : Configuration n -> Action n -> Configuration n -> Set where
  →c-comm :
    ∀ { lp lp′ lq lq′ c′ p≢q-p p≢q-q }
    -> (c : Configuration n)
    -> (p≢q : p ≢ q)
    -> lp ≡ lookup c p
    -> lq ≡ lookup c q
    -> c′ ≡ c [ p ]≔ lp′ [ q ]≔ lq′
    -> (p , lp) - (action p q p≢q-p l) →l (p , lp′)
    -> (q , lq) - (action p q p≢q-q l) →l (q , lq′)
    -> c - (action p q p≢q l) →c  c′
