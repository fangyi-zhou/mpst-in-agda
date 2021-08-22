module Common where

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

Label : Set
Label = ℕ

data Action (n : ℕ) : Set where
  action : (p q : Fin n) -> ¬ (p ≡ q) -> Label -> Action n

¬≡-flip : ∀ { l } { A : Set l } { x y : A } -> (x ≢ y) -> (y ≢ x)
¬≡-flip x≢y = λ y≡x → x≢y (sym y≡x)
