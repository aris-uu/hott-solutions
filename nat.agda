module nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

ℕ-rec : {C : Set} → C → (ℕ → C → C) → ℕ → C
ℕ-rec c0 cs zero = c0
ℕ-rec c0 cs (succ n) = cs n (ℕ-rec c0 cs n)