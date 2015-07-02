open import Empty

module Boolean where

  data Bool : Set where
    true : Bool
    false : Bool

  {-# BUILTIN BOOL Bool #-}
  {-# BUILTIN TRUE true #-}
  {-# BUILTIN FALSE false #-}

  T : Bool → Set
  T true = ⊤
  T false = ⊥

  not : Bool → Bool
  not true = false
  not false = true

  and : Bool → Bool → Bool
  and true true = true
  and _ _ = false

  or : Bool → Bool → Bool
  or false false = false
  or _ _ = true

  xor : Bool → Bool → Bool
  xor false true = true
  xor true false = true
  xor _ _ = false

  infixr 6 _∧_
  infixr 5 _∨_

  ¬_ : Set → Set
  ¬ A = A → ⊥

  data _∨_ A B : Set where
    Inl : A → A ∨ B
    Inr : B → A ∨ B

  data _∧_ A B : Set where
    Conj : A → B → A ∧ B

  _⇔_ : (P : Set) → (Q : Set) → Set
  a ⇔ b = (a → b) ∧ (b → a)

  ∧-symmetry : ∀ { A B : Set } → A ∧ B → B ∧ A
  ∧-symmetry (Conj x y) = Conj y x

  ∨-symmetry : ∀ { A B : Set } → A ∨ B → B ∨ A
  ∨-symmetry (Inl x) = Inr x
  ∨-symmetry (Inr y) = Inl y

  and_over : { A B C : Set } → A ∧ ( B ∨ C ) → ( A ∧ B ) ∨ ( A ∧ C )
  and_over (Conj x (Inl y)) = Inl (Conj x y)
  and_over (Conj x (Inr y)) = Inr (Conj x y)

  and_over' : { A B C : Set } → ( A ∧ B ) ∨ ( A ∧ C ) → A ∧ ( B ∨ C )
  and_over' (Inl (Conj x y)) = Conj x (Inl y)
  and_over' (Inr (Conj x y)) = Conj x (Inr y)

  or_over : { A B C : Set } → A ∨ ( B ∧ C ) → ( A ∨ B ) ∧ ( A ∨ C )
  or_over (Inl x) = Conj (Inl x) (Inl x)
  or_over (Inr (Conj x y)) = Conj (Inr x) (Inr y)

  or_over' : { A B C : Set } → ( A ∨ B ) ∧ ( A ∨ C ) → A ∨ ( B ∧ C )
  or_over' (Conj (Inl x) _) = Inl x
  or_over' (Conj _ (Inl y)) = Inl y
  or_over' (Conj (Inr x) (Inr y)) = Inr (Conj x y)

  or_over_negated : { A B : Set } → ( A ∨ ( ¬ A ∧ B ) ) → ( A ∨ B )
  or_over_negated (Inl x) = Inl x
  or_over_negated (Inr (Conj _ y)) = Inr y

  private
    proof₁ : { P Q : Set } → (P ∧ Q) → P
    proof₁ (Conj p q) = p

    proof₂ : { P Q : Set } → (P ∧ Q) → Q
    proof₂ (Conj p q) = q

  deMorgan₁ : { A B : Set } → ¬ A ∧ ¬ B → ¬ (A ∨ B)
  deMorgan₁ (Conj ¬x ¬y) (Inl x) = ¬x x
  deMorgan₁ (Conj ¬x ¬y) (Inr y) = ¬y y
  -- above is clearer if you re-write the type annotation as:
  --deMorgan₁ : { A B : Set } → (A → ⊥) ∧ (B → ⊥) → (A ∨ B) → ⊥

  deMorgan₂ : { A B : Set } → ¬ (A ∨ B) → ¬ A ∧ ¬ B
  deMorgan₂ z = Conj (λ x → z (Inl x)) (λ y → z (Inr y))

  deMorgan₃ : { A B : Set } → ¬ A ∨ ¬ B → ¬ (A ∧ B)
  deMorgan₃ (Inl ¬x) (Conj x _) = ¬x x
  deMorgan₃ (Inr ¬y) (Conj _ y) = ¬y y

  -- NOT provable.
  -- deMorgan₄ : { A B : Set } → ¬ (A ∧ B) → ¬ A ∨ ¬ B


