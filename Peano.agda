module Peano where

  Rel : Set → Set₁
  Rel X = X → X → Set

  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ
  {-# BUILTIN NATURAL ℕ #-}

  _+_ : ℕ → ℕ → ℕ
  zero + m = m
  (succ n) + m = succ (n + m)
  {-# BUILTIN NATPLUS _+_ #-}

  _∘_ : ℕ → ℕ → ℕ
  zero ∘ _ = zero
  (succ n) ∘ m = (n ∘ m) + m
  {-# BUILTIN NATTIMES _∘_ #-}

  pred : ℕ → ℕ
  pred zero = zero
  pred (succ x) = x

  data _even : ℕ → Set where
    ZERO : zero even
    STEP : ∀ {x} → x even → succ (succ x) even

  proof₁ : succ(succ(succ(succ(zero)))) even
  proof₁ = STEP (STEP ZERO)

  proof₂ : (A : Set) → A → A
  proof₂ _ ν = ν

  proof'₂ : ℕ → ℕ
  proof'₂ = proof₂ ℕ
