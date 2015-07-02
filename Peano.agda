open import Agda.Primitive
open import Empty
open import Logic
open import Boolean

module Peano where

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

  data _≡_ (x : ℕ) : ℕ → Set where
    refl : x ≡ x

  data _≢_ : ℕ → ℕ → Set where
    z≢s : ∀ {n} → zero ≢ succ n
    s≢z : ∀ {n} → succ n ≢ zero
    s≢s : ∀ {m n} → m ≢ n → succ m ≢ succ n

  data Equal? (m n : ℕ) : Set where
    yes : m ≡ n → Equal? m n
    no : m ≢ n → Equal? m n

  _≟_ : (m n : ℕ) → Equal? m n
  _≟_ zero zero = yes refl
  _≟_ zero (succ _) = no z≢s
  _≟_ (succ _) zero = no s≢z
  _≟_ (succ m) (succ n) with m ≟ n
  _≟_ (succ m) (succ .m) | yes refl = yes refl
  _≟_ (succ m) (succ n) | no p = no (s≢s p)

  equality-disjoint : (m n : ℕ) → m ≡ n → m ≢ n → ⊥
  equality-disjoint zero zero refl ()
  equality-disjoint zero (succ _) () z≢s
  equality-disjoint (succ _) zero () s≢z
  equality-disjoint (succ m) (succ .m) refl (s≢s e) = equality-disjoint m m refl e

  private
    -- to make the last `equality-disjoint` match clearer, verify that s≢s can be nested
    test-s≢s : (succ (succ (succ zero))) ≢ (succ (succ zero))
    test-s≢s = s≢s (s≢s s≢z)

  infix 4 _≤_ _<_ _≥_ _>_

  data _≤_ : Rel ℕ where
    z≤n : ∀ {n}                 → zero  ≤ n
    s≤s : ∀ {m n} (m≤n : m ≤ n) → succ m ≤ succ n

  _<_ : Rel ℕ
  m < n = succ m ≤ n

  _≥_ : Rel ℕ
  m ≥ n = n ≤ m

  _>_ : Rel ℕ
  m > n = n < m

  infix 4 _≤′_ _<′_ _≥′_ _>′_

  data _≤′_ (m : ℕ) : ℕ → Set where
    ≤′-refl :                         m ≤′ m
    ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ succ n

  _<′_ : Rel ℕ
  m <′ n = succ m ≤′ n

  _≥′_ : Rel ℕ
  m ≥′ n = n ≤′ m

  _>′_ : Rel ℕ
  m >′ n = n <′ m

  pred : ℕ → ℕ
  pred zero = zero
  pred (succ x) = x

  data _even : ℕ → Set where
    ZERO : zero even
    STEP : ∀ {x} → x even → succ (succ x) even

  private
    proof₁ : succ(succ(succ(succ(zero)))) even
    proof₁ = STEP (STEP ZERO)

    proof₂ : (A : Set) → A → A
    proof₂ _ ν = ν

    proof'₂ : ℕ → ℕ
    proof'₂ = proof₂ ℕ
