module IPL where

  data _∧_ (P : Set) (Q : Set) : Set where
    ∧-intro : P → Q → (P ∧ Q)

  proof₁ : { P Q : Set } → (P ∧ Q) → P
  proof₁ (∧-intro p q) = p

  proof₂ : { P Q : Set } → (P ∧ Q) → Q
  proof₂ (∧-intro p q) = q

  _⇔_ : (P : Set) → (Q : Set) → Set
  a ⇔ b = (a → b) ∧ (b → a)
