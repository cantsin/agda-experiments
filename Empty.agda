module Empty where

  record ⊤ : Set where
    constructor tt

  data ⊥ : Set where

  {-# IMPORT Data.FFI #-}
  {-# COMPILED_DATA ⊥ Data.FFI.AgdaEmpty #-}

  absurd : ∀ { A : Set } → ⊥ → A
  absurd ()
