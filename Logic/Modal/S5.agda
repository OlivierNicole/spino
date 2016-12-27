module Logic.Modal.S5 (W : Set) where

open import Relation.Nullary using () renaming (¬_ to ¬0_)
open import Data.Unit using () renaming (⊤ to ⊤0)
open import Data.Empty
  using (⊥-elim) renaming (⊥ to ⊥0)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using () renaming (_≡_ to _≡₀_ ; refl to refl₀ ; _≢_ to _≢₀_)

Prop : Set1
Prop = (w : W) → Set

private
  data _R_ : W → W → Set where
    refl : ∀ {w} → w R w
    sym : ∀ {w w'} → w R w' → w' R w
    trans : ∀ {w w' w''} → w R w' → w' R w'' → w R w''

infixr 30 ¬_
¬_ : Prop → Prop
(¬ P) w = ¬0 (P w)

infixl 10 _∧_
_∧_ : Prop → Prop → Prop
(P ∧ Q) w = P w × Q w

infixl 10 _∨_
_∨_ : Prop → Prop → Prop
(P ∨ Q) w = P w ⊎ Q w

infixr 5 _⇒_
_⇒_ : Prop → Prop → Prop
(P ⇒ Q) w = P w → Q w

m∀ : (A : Set) → (A → Prop) → Prop
m∀ A P w = (x : A) → P x w

infix 2 ∀₁-syntax
∀₁-syntax : (A : Set) → (A → Prop) → Prop
∀₁-syntax = m∀

syntax ∀₁-syntax A (λ x → P) = ∀₁[ x ∈ A ] P

m∃ : (A : Set) → (A → Prop) → Prop
m∃ _ P w = ∃ λ x → P x w

infix 2 ∃₁-syntax
∃₁-syntax : (A : Set) → (A → Prop) → Prop
∃₁-syntax = m∃

syntax ∃₁-syntax A (λ x → P) = ∃₁[ x ∈ A ] P

infixr 30 □_
□_ : Prop → Prop
(□ P) w = (w' : W)(wRw' : w R w') → P w'

infixr 30 ◇_
◇_ : Prop → Prop
(◇ P) w = ∃ (λ w' → w R w' × P w')

⊤ : Prop
⊤ w = ⊤0

⊥ : Prop
⊥ w = ⊥0

[_] : Prop → Set
[ P ] = {w : W} → P w

[[_]] : Set → Prop
[[ P ]] _ = P

⇒→ : ∀ {A B : Prop} → [ A ⇒ B ] → [ A ] → [ B ]
⇒→ A⇒B A = A⇒B A

K' : ∀ {A B : Prop} → [ □ (A ⇒ B) ] → [ □ A ] → [ □ B ]
K' □A⇒B □A {w} w' wRw' = □A⇒B w' wRw' (□A w' wRw')

K : ∀ {A B : Prop} → [ □ (A ⇒ B) ⇒ (□ A ⇒ □ B) ]
K □A⇒Bw □Aw w' wRw' = □A⇒Bw w' wRw' (□Aw w' wRw')

T : {A : Prop} → [ □ A ⇒ A ]
T {w = w} □A = □A w refl

□◇ : ∀ {A} → [ □ A ⇒ ◇ A ]
□◇ {w = w} z = w , refl , z w refl

A4 : ∀ {A} → [ □ A ⇒ □ □ A ]
A4 □Aw w' wRw' w'' w'Rw'' = □Aw w'' (trans wRw' w'Rw'')

B : ∀ {A} → [ A ⇒ □ ◇ A ]
B {w = w} Aw w' wRw' = w , sym wRw' , Aw

A5 : ∀ {A} → [ ◇ A ⇒ □ ◇ A ]
A5 ◇Aw w' wRw' with ◇Aw
... | w'' , wRw'' , Aw'' = w'' , trans (sym wRw') wRw'' , Aw''

◇⇒¬□¬ : ∀ {A} → [ ◇ A ⇒ ¬ □ ¬ A ]
◇⇒¬□¬ (w' , wRw' , Aw') □¬Aw = □¬Aw w' wRw' Aw'

¬□¬⇒¬¬◇ : ∀ {A} → [ ¬ □ ¬ A ⇒ ¬ ¬ ◇ A ]
¬□¬⇒¬¬◇ ¬□¬Aw ¬◇Aw = ¬□¬Aw (λ w' wRw' Aw' → ¬◇Aw (w' , wRw' , Aw'))

-- Equivalence
infixl 5 _⇔_
_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

-- Propositional equality, lifted
_≡₁_ : {A : Set} → A → A → Prop
x ≡₁ y = [[ x ≡₀ y ]]

_≢₁_ : {A : Set} → A → A → Prop
x ≢₁ y = [[ x ≢₀ y ]]

module Classical where
  postulate lem : (P : Prop) → [ P ∨ ¬ P ]

  dne : (P : Prop) → [ ¬ ¬ P ⇒ P ]
  dne P ¬¬P with lem P
  ... | (inj₁ Pw) = Pw
  ... | (inj₂ ¬Pw) = ⊥-elim (¬¬P ¬Pw)
