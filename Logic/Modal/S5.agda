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

-- Test.

x : □ ⊤
x = □-ax ⊤.tt

-- Axioms.

-- K (distribution).
K : ∀ {A B} → □(A → B) → (□ A → □ B)
K _ = λ z → □-ax □_.p _ (□_.p z)

-- T (also called M).
T : ∀ {A} → □ A → A
T (□-ax p) = p

-- 4
A4 : ∀ {A} → □ A → □ □ A
A4 p = □-ax p

-- 5
A5 : ∀ {A} → ◇ A → □ ◇ A
A5 p = □-ax p

-- Usual combinators.

open import Data.Product

_∧_ : ∀ {l} (P Q : Set l) → Set l
p ∧ q = p × q

_⇔_ : ∀ {l} (P Q : Set l) → Set l
p ⇔ q = (p → q) ∧ (q → p)
