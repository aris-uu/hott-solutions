{-# OPTIONS --type-in-type #-}

module chapter-1 where

open import identity
open import product
open import sigma

-- exercise 1.1

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

∘-assoc : {A B C D : Set} →
          (f : A → B)(g : B → C)(h : C → D) →
          h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc f g h = refl

-- exercise 1.2

-- product types

×-rec : {A B : Set} → (C : Set) → (A → B → C) → (A × B) → C
×-rec C f (a , b) = f a b

pr₁ : {A B : Set} → A × B → A
pr₁ (a , b) = a

pr₂ : {A B : Set} → A × B → B
pr₂ (a , b) = b

×-rec' : {A B : Set} → (C : Set) → (A → B → C) → (A × B) → C
×-rec' C g x = g (pr₁ x) (pr₂ x)

×-rec-equiv : {A B : Set} →
              (C : Set) →
              (g : A → B → C) →
              (a : A) → (b : B) →
              ×-rec' C g (a , b) ≡ g a b
×-rec-equiv C g a b = refl

-- sigma types

Σ-rec : {A : Set} → {B : A → Set} →
        (C : Set) →
        ((a : A) → B a → C) →
        Σ A B → C
Σ-rec C g (a , b) = g a b

pr₁' : {A : Set} {B : A → Set} → Σ A B → A
pr₁' (a , b) = a

pr₂' : {A : Set} {B : A → Set} → (p : Σ A B) → B (pr₁' p)
pr₂' (a , b) = b

Σ-rec' : {A : Set} → {B : A → Set} →
        (C : Set) →
        ((a : A) → B a → C) →
        Σ A B → C
Σ-rec' C g x = g (pr₁' x) (pr₂' x)

Σ-rec-equiv : {A : Set} → {B : A → Set} →
              (C : Set) →
              (g : (a : A) → B a → C) →
              (a : A) → (b : B a) →
              Σ-rec' C g (a , b) ≡ g a b
Σ-rec-equiv C g a b = refl

-- exercise 1.3

×-uniq : {A B : Set} → (x : A × B) → (pr₁ x , pr₂ x) ≡ x
×-uniq (a , b) = refl

transport : {A : Set}{P : A → Set}{x y : A} → (p : x ≡ y) → P x → P y
transport refl px = px

×-ind : {A B : Set} → (C : A × B → Set) → ((a : A) → (b : B) → C (a , b)) → (x : A × B) → C x
×-ind C g x = transport {_} {C} (×-uniq x) (g (pr₁ x) (pr₂ x))

-- exercise 1.11

data 𝟘 : Set where

¬_ : Set → Set
¬ A = A → 𝟘
infix 30 ¬_

¬¬ : Set → Set
¬¬ A = ¬ (¬ A)

¬¬¬ : Set → Set
¬¬¬ A = ¬ (¬¬ A)

ex1-11 : {A : Set} → ¬¬¬ A → ¬ A
ex1-11 = λ x x₁ → x λ x₂ → x₂ x₁

-- exercise 1.12

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

[i] : {A B : Set} → A → B → A
[i] a b = a

[ii] : {A : Set} → A → ¬¬ A
[ii] a na = na a

[iii] : {A B : Set} → (¬ A ⊕ ¬ B) → ¬ (A × B)
[iii] (inl na) (a , b) = na a
[iii] (inr nb) (a , b) = nb b

-- exercise 1.13

ex1-13 : {P : Set} → ¬¬ (P ⊕ ¬ P)
ex1-13 x = x (inr (λ p → x (inl p)))