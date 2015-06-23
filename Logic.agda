import Either
open import Boolean

module Logic where

  id : ∀ { A : Set } → A → A
  id x = x

  Rel : Set → Set₁
  Rel X = X → X → Set

  Decidable : ∀ { X } → Rel X → Set
  Decidable R = ∀ x y → Either (R x y) (¬ (R x y))
    where open Either

  modusPonens : { P Q : Set } → ( P → Q ) → P → Q
  modusPonens = id
