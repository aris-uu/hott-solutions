module identity where

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
  -- refl' : (a : A) → a ≡ a