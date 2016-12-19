open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Data.Product
open import Data.Sum

a : {P : Set} → ¬ ¬ (P ⊎ ¬ P)
a ¬P⊎¬P = ¬P⊎¬P (inj₂ (λ x → ¬P⊎¬P (inj₁ x)))

b : {P Q : Set} → ¬ ¬ ((¬ Q → ¬ P) → P → Q)
b {P} {Q} ¬[[¬Q→¬P]→P→Q] =
  ¬[[¬Q→¬P]→P→Q] b'
  where
  b' : (¬ Q → ¬ P) → P → Q
  b' ¬Q→¬P P = ⊥-elim (¬Q→¬P (λ Q → ¬[[¬Q→¬P]→P→Q] (λ _ _ → Q)) P)
