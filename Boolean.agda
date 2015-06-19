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

  data _∨_ { a b } ( A : Set a ) ( B : Set b ) : Set₁ where
    Inl : A → A ∨ B
    Inr : B → A ∨ B

  data _∧_ { a b } ( A : Set a ) ( B : Set b ) : Set₁ where
    Conj : A → B → A ∧ B

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
  or_over' (Conj (Inl x) (Inl y)) = Inl x
  or_over' (Conj (Inl x) (Inr y)) = Inl x
  or_over' (Conj (Inr x) (Inl y)) = Inl y
  or_over' (Conj (Inr x) (Inr y)) = Inr (Conj x y)
