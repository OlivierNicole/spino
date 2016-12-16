module Logic.Modal.S5 (W : Set) where

open import Relation.Nullary using () renaming (¬_ to ¬0_)
open import Data.Unit using () renaming (⊤ to ⊤0)
open import Data.Empty using () renaming (⊥ to ⊥0)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using () renaming (_≡_ to _≡₀_ ; refl to refl₀ ; _≢_ to _≢₀_)

Prop : Set1
Prop = (w : W) → Set

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

infixl 5 _⇒_
_⇒_ : Prop → Prop → Prop
(P ⇒ Q) w = P w → Q w

m∀ : {A : Set} → (A → Prop) → Prop
(m∀ P) w = ∀ x → P x w

m∃ : {A : Set} → (A → Prop) → Prop
(m∃ P) w = ∃ λ x → P x w

infixr 30 □_
□_ : Prop → Prop
(□ P) w = ∀ w' → w R w' → P w'

infixr 30 ◇_
◇_ : Prop → Prop
(◇ P) w = ∃ (λ w' → w R w' × P w')

⊤ : Prop
⊤ w = ⊤0

⊥ : Prop
⊥ w = ⊥0

[_] : Prop → Set
[ P ] = ∀ w → P w

[[_]] : Set → Prop
[[ P ]] _ = P

⇒→ : ∀ {A B : Prop} → [ A ⇒ B ] → [ A ] → [ B ]
⇒→ A⇒B A w = A⇒B w (A w)

→⇒ : ∀ {A B : Prop} → [ A ] → [ B ] → [ A ⇒ B ]
→⇒ A B w Aw = B w

K' : ∀ {A B : Prop} → [ □ (A ⇒ B) ] → [ □ A ] → [ □ B ]
K' □A⇒B □A w w' x = □A⇒B w w' x (□A w w' x)

K : ∀ {A B : Prop} → [ □ (A ⇒ B) ⇒ (□ A ⇒ □ B) ]
K w □A⇒Bw □Aw w' wRw' = □A⇒Bw w' wRw' (□Aw w' wRw')

typ : ∀ (A B : Prop) → Set₁
typ A B = □ (A ⇒ B) ⇒ (□ A ⇒ □ B)

T : ∀ {A} → [ □ A ⇒ A ]
T w z = z w refl

□◇ : ∀ {A} → [ □ A ⇒ ◇ A ]
□◇ w z = w , refl , z w refl

A4 : ∀ {A} → [ □ A ⇒ □ □ A ]
A4 w □Aw w' wRw' w'' w'Rw'' = □Aw w'' (trans wRw' w'Rw'')

B : ∀ {A} → [ A ⇒ □ ◇ A ]
B w Aw w' wRw' = w , sym wRw' , Aw

A5 : ∀ {A} → [ ◇ A ⇒ □ ◇ A ]
A5 w ◇Aw w' wRw' with ◇Aw
A5 w ◇Aw w' wRw' | w'' , wRw'' , Aw'' = w'' , trans (sym wRw') wRw'' , Aw''

foo : ∀ {A} → [ ◇ A ⇒ ¬ □ ¬ A ]
foo w ◇Aw □¬Aw with ◇Aw
foo w ◇Aw □¬Aw | w' , wRw' , Aw' = □¬Aw w' wRw' Aw'

bar : ∀ {A} → [ ¬ □ ¬ A ⇒ ¬ ¬ ◇ A ]
bar w ¬□¬Aw ¬◇Aw = ¬□¬Aw (λ w' wRw' Aw' → ¬◇Aw (w' , wRw' , Aw'))

-- Equivalence
_⇔_ : Prop → Prop → Prop
P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

-- Propositional equality, lifted
_≡₁_ : {A : Set} → A → A → Prop
x ≡₁ y = [[ x ≡₀ y ]]

_≢₁_ : {A : Set} → A → A → Prop
x ≢₁ y = [[ x ≢₀ y ]]
