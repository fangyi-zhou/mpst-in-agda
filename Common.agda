module Common where

open import Data.Nat using (ℕ)

Role : Set
Role = ℕ

Label : Set
Label = ℕ

data Action : Set where
  AMsg : (p q : Role) -> Label -> Action
