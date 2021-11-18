module Common where

open import Level using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

private
  variable
    l : Level
    A : Set l
    x x′ y : A

Label : Set
Label = ℕ

data Action (n : ℕ) : Set where
  action : (p q : Fin n) -> p ≢ q -> Label -> Action n

¬≡-flip : x ≢ y -> y ≢ x
¬≡-flip x≢y = λ y≡x → x≢y (sym y≡x)

≢-subst-left : x ≢ y -> x ≡ x′ -> x′ ≢ y
≢-subst-left x≢y refl = x≢y

≢-subst-right : y ≢ x -> x ≡ x′ -> y ≢ x′
≢-subst-right y≢x refl = y≢x
