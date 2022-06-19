open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Fin using (Fin; fromℕ; inject₁)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; lookup; _[_]≔_)

open import Common

{- n sets the number of participants, t is the deBruijn index of recursive variable -}
interleaved mutual
  data Local (n : ℕ) (t : ℕ) : Set
  data GuardedL {n t} : (target : Fin t) -> Local n t -> Set

  data Local n t where
    endL : Local n t
    sendSingle recvSingle : Fin n -> Label -> Local n t -> Local n t
    recL : (l : Local n (suc t)) -> GuardedL (fromℕ t) l -> Local n t
    varL : (recVar : Fin t) -> Local n t

  data GuardedL target l where
    endLocal : ∀{target} -> GuardedL target endL
    send : ∀{p l lSub target} -> GuardedL target (sendSingle p l lSub)
    recv : ∀{p l lSub target} -> GuardedL target (recvSingle p l lSub)
    guardedVarL : ∀{target} {x : Fin t} -> target ≢ x -> GuardedL target (varL x)
    guardedRecL : ∀{target l guarded} -> GuardedL target (recL l guarded)

private
  variable
    n : ℕ
    t : ℕ
    p p′ q : Fin n
    p≢q : p ≢ q
    l l′ : Label
    lSub lSub′ : Local n t

endL≢sendSingle : endL ≢ sendSingle p l lSub
endL≢sendSingle ()

endL≢recvSingle : endL ≢ recvSingle p l lSub
endL≢recvSingle ()

sendSingle-injective :
  sendSingle {n} {t} p l lSub ≡ sendSingle p′ l′ lSub′
  -> p ≡ p′ × l ≡ l′ × lSub ≡ lSub′
sendSingle-injective refl = refl , refl , refl

recvSingle-injective :
  recvSingle {n} p l lSub ≡ recvSingle p′ l′ lSub′
  -> p ≡ p′ × l ≡ l′ × lSub ≡ lSub′
recvSingle-injective refl = refl , refl , refl

{-
muL-injective :
  ∀{guarded guarded′} ->
  muL {n} {t} lSub guarded ≡ muL lSub′ guarded′
  -> lSub ≡ lSub′
muL-injective refl = refl
--}

{- Configuration should not contain open types -}
Configuration : ℕ -> Set
Configuration n = Vec (Local n zero) n

{- Reduction is only defined over closed local types -}
data _-_→l_ {n : ℕ} : (Fin n × Local n zero) -> Action n -> (Fin n × Local n zero) -> Set where
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
