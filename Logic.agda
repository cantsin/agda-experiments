import Either

module Logic where

  data Empty : Set where

  infix 3 ¬_
  ¬_ : Set → Set
  ¬_ X = X → Empty

  Rel : Set → Set₁
  Rel X = X → X → Set

  Decidable : ∀ {X} → Rel X → Set
  Decidable R = ∀ x y → Either (R x y) (¬ (R x y))
    where open Either
