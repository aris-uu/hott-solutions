module identity where

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
  -- refl' : (a : A) → a ≡ a

inv : {A : Set}{x y : A} → x ≡ y → y ≡ x
inv refl = refl

_∙_ : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ refl = refl

ap : {A B : Set}{x y : A} → (f : A → B) → (x ≡ y) → (f x ≡ f y)
ap f refl = refl

transport : {A : Set}{P : A → Set}{x y : A} → (p : x ≡ y) → P x → P y
transport refl px = px