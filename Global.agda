open import Common using (Role; Label)

data Global : Set where
    End : Global
    MsgSingle : Role -> Role -> Label -> Global -> Global
