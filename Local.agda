open import Common using (Role; Label; Action; AMsg)

data Local : Set where
    End : Local
    Send Recv : Role -> Label -> Local -> Local

record NamedLocal : Set where
    constructor _,_
    field
        role : Role
        local : Local

data _-_→l_ : NamedLocal -> Action -> NamedLocal -> Set where
    LSend : ∀{p q l lt' p≠q} -> (p , Send q l lt') - (AMsg p q p≠q l) →l (p , lt')
    LRecv : ∀{p q l lt' p≠q} -> (q , Recv q l lt') - (AMsg p q p≠q l) →l (q , lt')
