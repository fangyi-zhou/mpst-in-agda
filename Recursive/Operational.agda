{-# OPTIONS --guardedness #-}

module Recursive.Operational where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (Vec; lookup; _[_]≔_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Common
open import Recursive.Base
open import Recursive.Coinductive
open import Recursive.Projection

private
  variable
    n ℓ Γ : ℕ
    p q r s : Fin n
    label label′ : Fin ℓ
    p≢q r≢s : p ≢ q

infix 4 _-_→rg_ _-_→rl_ _-_→rc_ _-_→cg_ _-_→cl_ _-_→cc_

data _-_→rg_ {n ℓ Γ : ℕ} : RGlobal n ℓ Γ -> Action n ℓ -> RGlobal n ℓ Γ -> Set where
  →rg-prefix :
    ∀ {p q p≢q p≢q′ label g}
    -> (msgSingleRG p q p≢q label g) - (action p q p≢q′ label) →rg g
  →rg-cont :
    ∀ {p q r s p≢q r≢s label label′ g g′}
    -> g - (action p q p≢q label) →rg g′
    -> p ≢ r
    -> q ≢ r
    -> p ≢ s
    -> q ≢ s
    -> (msgSingleRG r s r≢s label′ g) - (action p q p≢q label) →rg
       (msgSingleRG r s r≢s label′ g′)
  →rg-unfold :
    ∀ {g g′ act}
    -> unfoldRG (muRG g) - act →rg g′
    -> muRG g - act →rg g′

data _-_→rl_ {n ℓ Γ : ℕ} : (Fin n × RLocal n ℓ Γ) -> Action n ℓ -> (Fin n × RLocal n ℓ Γ) -> Set where
  →rl-send :
    ∀ {lp lpSub p q p≢q label}
    -> lp ≡ sendSingleRL q label lpSub
    -> (p , lp) - (action p q p≢q label) →rl (p , lpSub)
  →rl-recv :
    ∀ {lp lpSub p q q≢p label}
    -> lp ≡ recvSingleRL q label lpSub
    -> (p , lp) - (action q p q≢p label) →rl (p , lpSub)
  →rl-unfold :
    ∀ {p l l′ act}
    -> (p , unfoldRL (muRL l)) - act →rl (p , l′)
    -> (p , muRL l) - act →rl (p , l′)

data _-_→rc_ {n ℓ Γ : ℕ} : RConfiguration n ℓ Γ -> Action n ℓ -> RConfiguration n ℓ Γ -> Set where
  →rc-comm :
    ∀ {p q label lp lp′ lq lq′ c′ p≢q-p p≢q-q}
    -> (c : RConfiguration n ℓ Γ)
    -> (p≢q : p ≢ q)
    -> lp ≡ lookup c p
    -> lq ≡ lookup c q
    -> c′ ≡ c [ p ]≔ lp′ [ q ]≔ lq′
    -> (p , lp) - (action p q p≢q-p label) →rl (p , lp′)
    -> (q , lq) - (action p q p≢q-q label) →rl (q , lq′)
    -> c - (action p q p≢q label) →rc c′

coMsgG : (p q : Fin n) -> p ≢ q -> Fin ℓ -> CoGlobal n ℓ -> CoGlobal n ℓ
coMsgG p q p≢q label g .observeG = msgSingleCG p q p≢q label g

coSendL coRecvL : Fin n -> Fin ℓ -> CoLocal n ℓ -> CoLocal n ℓ
coSendL p label l .observeL = sendSingleCL p label l
coRecvL p label l .observeL = recvSingleCL p label l

CoConfiguration : ℕ -> ℕ -> Set
CoConfiguration n ℓ = Vec (CoLocal n ℓ) n

data _-_→cg_ {n ℓ : ℕ} : CoGlobal n ℓ -> Action n ℓ -> CoGlobal n ℓ -> Set where
  →cg-prefix :
    ∀ {g g′ p q p≢q p≢q′ label}
    -> observeG g ≡ msgSingleCG p q p≢q label g′
    -> g - (action p q p≢q′ label) →cg g′
  →cg-cont :
    ∀ {g gSub gSub′ p q r s p≢q r≢s label label′}
    -> observeG g ≡ msgSingleCG r s r≢s label′ gSub
    -> gSub - (action p q p≢q label) →cg gSub′
    -> p ≢ r
    -> q ≢ r
    -> p ≢ s
    -> q ≢ s
    -> g - (action p q p≢q label) →cg coMsgG r s r≢s label′ gSub′

data _-_→cl_ {n ℓ : ℕ} : (Fin n × CoLocal n ℓ) -> Action n ℓ -> (Fin n × CoLocal n ℓ) -> Set where
  →cl-send :
    ∀ {p q p≢q label l l′}
    -> observeL l ≡ sendSingleCL q label l′
    -> (p , l) - (action p q p≢q label) →cl (p , l′)
  →cl-recv :
    ∀ {p q q≢p label l l′}
    -> observeL l ≡ recvSingleCL q label l′
    -> (p , l) - (action q p q≢p label) →cl (p , l′)

data _-_→cc_ {n ℓ : ℕ} : CoConfiguration n ℓ -> Action n ℓ -> CoConfiguration n ℓ -> Set where
  →cc-comm :
    ∀ {p q label lp lp′ lq lq′ c′ p≢q-p p≢q-q}
    -> (c : CoConfiguration n ℓ)
    -> (p≢q : p ≢ q)
    -> lp ≡ lookup c p
    -> lq ≡ lookup c q
    -> c′ ≡ c [ p ]≔ lp′ [ q ]≔ lq′
    -> (p , lp) - (action p q p≢q-p label) →cl (p , lp′)
    -> (q , lq) - (action p q p≢q-q label) →cl (q , lq′)
    -> c - (action p q p≢q label) →cc c′
