module Logic.Modal.S5 where

open import Relation.Nullary using (¬_) public
open import Data.Unit using (⊤) public
open import Data.Empty using (⊥) public
open import Agda.Primitive using (Level)

-- Modal operators.

infixr 3 □_
record □_ {l : Level}(A : Set l) : Set l where
  constructor □-ax_
  field
    p : A

infixr 3 ◇_
◇_ : ∀ {l} → Set l → Set l
◇ p = ¬ □ ¬ p

-- Axioms.

-- K (distribution).
K : ∀ {l} {A B : Set l} → □(A → B) → (□ A → □ B)
K (□-ax p) (□-ax p₁) = □-ax (p p₁)

-- T (also called M).
T : ∀ {l} {A : Set l} → □ A → A
T (□-ax p) = p

-- 4
A4 : ∀ {l} {A : Set l} → □ A → □ □ A
A4 p = □-ax p

-- 5
A5 : ∀ {l} {A : Set l} → ◇ A → □ ◇ A
A5 p = □-ax p

-- Usual combinators.

open import Data.Product

_∧_ : ∀ {l} (P Q : Set l) → Set l
p ∧ q = p × q

_⇔_ : ∀ {l} (P Q : Set l) → Set l
p ⇔ q = (p → q) ∧ (q → p)
