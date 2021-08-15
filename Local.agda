open import Relation.Binary.PropositionalEquality using (subst; _≡_)
open import Relation.Nullary using (¬_)
open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Data.Nat.Properties using (<-strictTotalOrder)
import Data.Tree.AVL <-strictTotalOrder as Map
open Map using (_,_)

open import Common using (Role; Label; Action; AMsg)

data Local : Set where
    End : Local
    Send Recv : Role -> Label -> Local -> Local

Local' = Map.MkValue (λ _ -> Local) (subst (λ _ -> Local))

Configuration : Set
Configuration = Map.Tree Local'

data _-_→l_ : Map.K& Local' -> Action -> Map.K& Local' -> Set where
    LSend : ∀{p q l lt' p≠q} -> (p , Send q l lt') - (AMsg p q p≠q l) →l (p , lt')
    LRecv : ∀{p q l lt' p≠q} -> (q , Recv p l lt') - (AMsg p q p≠q l) →l (q , lt')

data _-_→c_ : Configuration -> Action -> Configuration -> Set where
    CComm : ∀{p q l lp lq lp' lq'}
             -> (c : Configuration)
             -> (p≠q : ¬ (p ≡ q))
             -> Map.lookup p c ≡ just lp
             -> Map.lookup q c ≡ just lq
             -> (p , lp) - (AMsg p q p≠q l) →l (p , lp')
             -> (q , lq) - (AMsg p q p≠q l) →l (q , lq')
             -> c - (AMsg p q p≠q l) →c (Map.insert p lp' (Map.insert q lq' c))
