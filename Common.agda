module Common where

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

Label : Set
Label = ℕ

data Action (n : ℕ) : Set where
  action : (p q : Fin n) -> ¬ (p ≡ q) -> Label -> Action n
