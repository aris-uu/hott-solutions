data Bool : Set where
  false : Bool
  true : Bool

bool-rec : {C : Set} → C → C → Bool → C
bool-rec a b false = a
bool-rec a b true = b