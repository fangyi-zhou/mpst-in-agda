module Common where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; refl)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

Label : Set
Label = ℕ

data Action (n : ℕ) : Set where
  action : (p q : Fin n) -> (p ≢ q) -> Label -> Action n

¬≡-flip : ∀ { l } { A : Set l } { x y : A } -> (x ≢ y) -> (y ≢ x)
¬≡-flip x≢y = λ y≡x → x≢y (sym y≡x)

≢-subst-left : ∀ { A : Set } { x x′ y : A } -> x ≢ y -> x ≡ x′ -> x′ ≢ y
≢-subst-left x≢y refl = x≢y

≢-subst-right : ∀ { A : Set } { x x′ y : A } -> y ≢ x -> x ≡ x′ -> y ≢ x′
≢-subst-right y≢x refl = y≢x
