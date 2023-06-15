module product where

open import sigma
open import identity

-- data _×_ (A B : Set) : Set where
--   _,_ : A → B → A × B

-- product type is a special case of the sigma type

_×_ : (A B : Set) → Set
A × B = Σ A (λ x → B)

×-rec : {A B : Set} → (C : Set) → (A → B → C) → (A × B) → C
×-rec C f (a , b) = f a b

×-uniq : {A B : Set} → (x : A × B) → (pr₁ x , pr₂ x) ≡ x
×-uniq (a , b) = refl

×-ind : {A B : Set} →
         (C : A × B → Set) →
         ((a : A) → (b : B) → C (a , b)) →
         (x : A × B) → C x
×-ind C g (a , b) = g a b