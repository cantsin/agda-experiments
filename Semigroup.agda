open import Peano using (ℕ; zero; succ; _+_; Rel)

module Semigroup where

  infix 4 _≡_

  data _≡_ {a} {A : Set a} (x : A) : A → Set a where
    refl : x ≡ x

  record Semigroup {A : Set} (_◇_ : A → A → A) : Set where
    field
      associativity : ∀ x y z → (x ◇ y) ◇ z ≡ x ◇ (y ◇ z)

  record ℕ+-isSemigroup : Semigroup _+_ where
    field
      associativity : ∀ x y z → (x + y) + z ≡ x + (y + z)
