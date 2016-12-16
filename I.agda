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
-- 1A4 estas, fakte, difino, kaj diras ke _⊢_ ≡ _konc_
_konc_ : Ω → Ω → Prop
_konc_ = _⊢_

-- 1D3
subst : Ω → Prop
subst x = x ⊆ x ∧ x konc x

-- 1D2
-- 1D2, fakte, difinas finieco en sia ĝenro.
--finia : Ω → Prop
--finia x = [ m∃ (λ y → (y ≢₁ x ∧ x ≤ y) ∧ m∀ (λ z → )) ]
