open import Common using (Role; Label)

data Local : Set where
    End : Local
    Send Recv : Role -> Label -> Local -> Local
