module Semigroup where

  infix 4 _≡_

  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

  record Semigroup {A : Set} (_◇_ : A → A → A) : Set where
    field
      associativity : ∀ x y z → (x ◇ y) ◇ z ≡ x ◇ (y ◇ z)
