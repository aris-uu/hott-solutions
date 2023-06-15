module chapter-2 where

open import identity

-- exercise 2.1

_∙₁_ : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙₁ q = q 

_∙₂_ : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
p ∙₂ refl = p

_∙₃_ : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙₃ refl = refl

eq1 : {A : Set}{x y z : A}(p : x ≡ y)(q : y ≡ z) → p ∙₁ q ≡ p ∙₂ q
eq1 refl refl = refl

eq2 : {A : Set}{x y z : A}(p : x ≡ y)(q : y ≡ z) → p ∙₁ q ≡ p ∙₃ q
eq2 refl refl = refl

eq3 : {A : Set}{x y z : A}(p : x ≡ y)(q : y ≡ z) → p ∙₂ q ≡ p ∙₃ q
eq3 refl refl = refl

-- exercise 2.2

triangle : {A : Set}{x y z : A}(p : x ≡ y)(q : y ≡ z) → (eq1 p q) ∙ (eq3 p q) ≡ (eq2 p q)
triangle refl refl = refl