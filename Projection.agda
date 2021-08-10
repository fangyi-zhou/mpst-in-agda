open import Data.Bool using (true; false)
open import Data.Nat using (_≡ᵇ_)
open import Common using (Role; Label)
open import Global using (Global)
open import Local using (Local)

project : Global -> Role -> Local
project Global.End r = Local.End
project (Global.MsgSingle p q l g) r with p ≡ᵇ r | q ≡ᵇ r
...                                     | true   | false = Local.Send q l (project g r)
...                                     | false  | true  = Local.Recv p l (project g r)
...                                     | false  | false = project g r
{- TODO: Find a way to say p ≠ q -}
