module Common where

open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat using (ℕ)

Role : Set
Role = ℕ

Label : Set
Label = ℕ

data Action : Set where
  AMsg : (p q : Role) -> ¬ (p ≡ q) -> Label -> Action
