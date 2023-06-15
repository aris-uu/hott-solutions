module sigma where

data Σ (A : Set)(B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

Σ-rec : {A : Set} → {B : A → Set} →
        (C : Set) →
        ((a : A) → B a → C) →
        Σ A B → C
Σ-rec C g (a , b) = g a b

pr₁ : {A : Set} {B : A → Set} → Σ A B → A
pr₁ (a , b) = a

pr₂ : {A : Set} {B : A → Set} → (p : Σ A B) → B (pr₁ p)
pr₂ (a , b) = b