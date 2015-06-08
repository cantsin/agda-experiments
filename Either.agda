module Either where

  data Either (A : Set) (B : Set) : Set where
    left : A → Either A B
    right : B → Either A B

  [_,_] : ∀ {A B} {C : Set} → (A → C) → (B → C) → Either A B → C
  [ f , g ] (left x)  = f x
  [ f , g ] (right x) = g x
