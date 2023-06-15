{-# OPTIONS --type-in-type #-}

module chapter-1 where

open import identity
open import product
open import sigma
open import nat

-- exercise 1.1

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

∘-assoc : {A B C D : Set} →
          (f : A → B)(g : B → C)(h : C → D) →
          h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
∘-assoc f g h = refl

-- exercise 1.2

-- product types

×-rec' : {A B : Set} → (C : Set) → (A → B → C) → (A × B) → C
×-rec' C g x = g (pr₁ x) (pr₂ x)

×-rec-equiv : {A B : Set} →
              (C : Set) →
              (g : A → B → C) →
              (a : A) → (b : B) →
              ×-rec' C g (a , b) ≡ g a b
×-rec-equiv C g a b = refl

-- sigma types

Σ-rec' : {A : Set} → {B : A → Set} →
        (C : Set) →
        ((a : A) → B a → C) →
        Σ A B → C
Σ-rec' C g x = g (pr₁ x) (pr₂ x)

Σ-rec-equiv : {A : Set} → {B : A → Set} →
              (C : Set) →
              (g : (a : A) → B a → C) →
              (a : A) → (b : B a) →
              Σ-rec' C g (a , b) ≡ g a b
Σ-rec-equiv C g a b = refl

-- exercise 1.3

×-ind' : {A B : Set} → (C : A × B → Set) → ((a : A) → (b : B) → C (a , b)) → (x : A × B) → C x
×-ind' C g x = transport {_} {C} (×-uniq x) (g (pr₁ x) (pr₂ x))

-- exercise 1.4

iter : {C : Set} → C → (C → C) → ℕ → C
iter c0 cs zero = c0
iter c0 cs (succ x) = cs (iter c0 cs x)

cs' : {C : Set} → (ℕ → C → C) → C × ℕ → C × ℕ
cs' cs (c' , x') = cs x' c' , succ x'

ℕ-rec' : {C : Set} → C → (ℕ → C → C) → ℕ → C
ℕ-rec' {C} c0 cs x = pr₁ (iter {C × ℕ} (c0 , zero) (cs' cs) x)

ℕ-rec-α : {C : Set} → (c0 : C) → (cs : ℕ → C → C) → ℕ-rec' c0 cs zero ≡ c0
ℕ-rec-α c0 cs = refl

iter-lemma : {C : Set} → (c0 : C) → (cs : ℕ → C → C) →
  (n : ℕ) → iter (c0 , zero) (cs' cs) n ≡ (ℕ-rec c0 cs n , n)
iter-lemma c0 cs zero = refl
iter-lemma c0 cs (succ n) = ap (λ x → cs' cs x) (iter-lemma c0 cs n)

iter-lemma1 : {C : Set} → (c0 : C) → (cs : ℕ → C → C) →
  (n : ℕ) → ℕ-rec' c0 cs n ≡ ℕ-rec c0 cs n
iter-lemma1 c0 cs n = ap pr₁ (iter-lemma c0 cs n)

ℕ-rec-β : {C : Set} → (c0 : C) → (cs : ℕ → C → C) → (n : ℕ) → ℕ-rec' c0 cs (succ n) ≡ cs n (ℕ-rec' c0 cs n)
ℕ-rec-β c0 cs n = iter-lemma1 c0 cs (succ n) ∙ inv (ap (cs n) (iter-lemma1 c0 cs n))

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