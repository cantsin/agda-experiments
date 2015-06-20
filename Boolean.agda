module Boolean where

  record ⊤ : Set where
    constructor tt

  data ⊥ : Set where

  {-# IMPORT Data.FFI #-}
  {-# COMPILED_DATA ⊥ Data.FFI.AgdaEmpty #-}

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

  data ¬_ A : Set where
    Neg : A → ¬ A

  -- ¬_ : Set → Set
  -- ¬ A = A → ⊥

  data _∨_ A B : Set where
    Inl : A → A ∨ B
    Inr : B → A ∨ B

  data _∧_ A B : Set where
    Conj : A → B → A ∧ B

  ∧-symmetry : ∀ { A B : Set } → A ∧ B → B ∧ A
  ∧-symmetry (Conj x y) = Conj y x

  ∨-symmetry : ∀ { A B : Set } → A ∨ B → B ∨ A
  ∨-symmetry (Inl x) = Inr x
  ∨-symmetry (Inr y) = Inl y

  -- still doesn't seem right.
  and_neg : { A : Set } → ( A ∧ ¬ A ) → Set
  and_neg _ = ⊥

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

  demorgan : { A B : Set } → ¬ A ∧ ¬ B → ¬ ( A ∨ B )
  demorgan (Conj (Neg x) _) = Neg (Inl x)
