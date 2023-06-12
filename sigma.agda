module sigma where

data Σ (A : Set)(B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B