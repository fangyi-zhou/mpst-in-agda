open import Common using (Role; Label)

data Global : Set where
    g_end : Global
    g_msg_single : Role -> Role -> Label -> Global
