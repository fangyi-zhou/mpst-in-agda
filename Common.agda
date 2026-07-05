module Common where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; _≟_)
open import Data.Vec using (Vec; lookup; _[_]≔_)
open import Data.Vec.Properties using (lookup∘update; lookup∘update′)

private
  variable
    n ℓ : ℕ
    l : Level
    A : Set l
    x x′ y : A

data Action (n : ℕ) (ℓ : ℕ) : Set where
  action : (p q : Fin n) -> p ≢ q -> Fin ℓ -> Action n ℓ

action′ : (p q : Fin n) -> {False (p ≟ q)} -> Fin ℓ -> Action n ℓ
action′ p q {p≢q} l = action p q (toWitnessFalse p≢q) l

¬≡-flip : x ≢ y -> y ≢ x
¬≡-flip x≢y = λ y≡x → x≢y (sym y≡x)

≢-subst-left : x ≢ y -> x ≡ x′ -> x′ ≢ y
≢-subst-left x≢y refl = x≢y

≢-subst-right : y ≢ x -> x ≡ x′ -> y ≢ x′
≢-subst-right y≢x refl = y≢x

lookup-update₂-left :
  (xs : Vec A n)
  -> (i j : Fin n)
  -> i ≢ j
  -> (x y : A)
  -> lookup ((xs [ i ]≔ x) [ j ]≔ y) i ≡ x
lookup-update₂-left xs i j i≢j x y
  rewrite lookup∘update′ i≢j (xs [ i ]≔ x) y
  rewrite lookup∘update i xs x
  = refl

lookup-update₂-right :
  (xs : Vec A n)
  -> (i j : Fin n)
  -> (x y : A)
  -> lookup ((xs [ i ]≔ x) [ j ]≔ y) j ≡ y
lookup-update₂-right xs i j x y
  rewrite lookup∘update j (xs [ i ]≔ x) y
  = refl

lookup-update₂-other :
  (xs : Vec A n)
  -> (i j k : Fin n)
  -> k ≢ i
  -> k ≢ j
  -> (x y : A)
  -> lookup ((xs [ i ]≔ x) [ j ]≔ y) k ≡ lookup xs k
lookup-update₂-other xs i j k k≢i k≢j x y
  rewrite lookup∘update′ k≢j (xs [ i ]≔ x) y
  rewrite lookup∘update′ k≢i xs x
  = refl
