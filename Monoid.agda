open import Agda.Primitive
open import Semigroup

module Monoid where

  record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
    constructor _,_
    field
      proj₁ : A
      proj₂ : B proj₁

  Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
  Σ-syntax = Σ

  syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

  _×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
  A × B = Σ[ x ∈ A ] B

  record Monoid {A : Set} (_∙_ : A → A → A) (ε : A) : Set where
    field
      semigroup : Semigroup _∙_
      identity : (∀ x → ε ∙ x ≡ x) × (∀ x → x ∙ ε ≡ x)
