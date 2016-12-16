-- Etiko, Parto I.
module I where

import Logic.Modal.S5

-- Aksiomoj.
record Aksiomoj₁ : Set₁ where
  field
    -- Ekzistas aro de eblaj mondoj.
    W : Set
    -- Ekzistas aro de ĉiuj aĵo, pri kio temas en la Etiko.
    Ω : Set

  open Logic.Modal.S5 W public

  field
    -- Primitivaj predikatoj.
    -- x ⊢ y : x kaŭzas y.
    _⊢_ : Ω → Ω → Prop
    -- x ≤ y : y randas x.
    _≤_ : Ω → Ω → Prop
    -- x ⊆ y : x estas en y.
    _⊆_ : Ω → Ω → Prop

    -- 1D1 estas, fakte, aksiomo.
    1D1 : {x : Ω} →
      [ x ⊢ x ∧ ¬ m∃ (λ y → y ≢₁ x ∧ x ⊢ y) ⇔ □ m∃ (λ y → y ≡₁ x) ]

postulate aksiomoj₁ : Aksiomoj₁
open Aksiomoj₁ aksiomoj₁

-- 1A4
-- 1A4 estas, fakte, difino, kaj diras ke x ⊢ y ≡ y konc-per x
_konc-per_ : Ω → Ω → Prop
x konc-per y = y ⊢ x

-- 1D3
subst : Ω → Prop
subst x = x ⊆ x ∧ x konc-per x

-- 1D4a
atr : Ω → Prop
atr x = m∃ (λ y → subst y ∧ x ⊆ y ∧ x konc-per y ∧ y ⊆ x ∧ y konc-per x)

-- 1D4b
_atr-of_ : Ω → Ω → Prop
x atr-of y = atr x ∧ y konc-per x

-- 1D2
finia : Ω → Prop
finia x = m∃ (λ y → y ≢₁ x ∧ x ≤ y ∧ m∀ (λ z → (z atr-of x) ⇔ (z atr-of y)))

-- 1D5a
_moduso-de_ : Ω → Ω → Prop
x moduso-de y = x ≢₁ y ∧ x ⊆ y ∧ x konc-per y

-- 1D5b
moduso : Ω → Prop
moduso x = m∃ (λ y → subst y ∧ x moduso-de y)

-- 1D6
deo : Ω → Prop
deo x = subst x ∧ m∀ λ y → atr y ⇒ y atr-of x

-- 1D7
lib : Ω → Prop
lib x = x ⊢ x ∧ ¬ m∃ λ y → y ≢₁ x ∧ y ⊢ x

nec : Ω → Prop
nec x = m∃ λ y → y ≢₁ x ∧ y ⊢ x

-- 1D8
eterna : Ω → Prop
eterna x = □ m∃ λ y → y ≡₁ x
