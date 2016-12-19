-- Etiko, Parto I.
module I where

import Logic.Modal.S5
open import Data.Product
open import Data.Sum
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_)

record Primitivoj : Set₁ where
  field
    -- Ekzistas aro de eblaj mondoj.
    W : Set
    -- Ekzistas aro de ĉiuj aĵoj, pri kio temas en la Etiko.
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
    -- x kom-al y kaj z : x estas komuna al y kaj z.
    _kom-al_kaj_ : Ω → Ω → Ω → Prop
    -- x ak y : x akordiĝas kun y.
    _ak_ : Ω → Ω → Prop
    -- ideo x : x estas ideo.
    ideo : Ω → Prop
    -- vera x : x estas vera (uzata pri ideoj).
    vera : Ω → Prop
    -- x objekto y : x estas objekto de y.
    _objekto_ : Ω → Ω → Prop

postulate primitivoj : Primitivoj
open Primitivoj primitivoj

-- 1D1 estas, fakte, aksiomo (v. malalte).

-- 1D2 necesas 1D4b (v. malalte).

-- 1A4
-- 1A4 estas, fakte, difino, kaj diras ke x ⊢ y ≡ y konc-per x.
_konc-per_ : Ω → Ω → Prop
x konc-per y = y ⊢ x

-- 1D3
subst : Ω → Prop
subst x = x ⊆ x ∧ x konc-per x

-- 1D4a
atr : Ω → Prop
atr x = ∃₁[ y ∈ Ω ] subst y ∧ x ⊆ y ∧ x konc-per y ∧ y ⊆ x ∧ y konc-per x

-- 1D4b
_atr-of_ : Ω → Ω → Prop
x atr-of y = atr x ∧ y konc-per x

-- 1D2
finia : Ω → Prop
finia x =
  ∃₁[ y ∈ Ω ] y ≢₁ x ∧ x ≤ y ∧ (∀₁[ z ∈ Ω ] (z atr-of x) ⇔ (z atr-of y))

-- 1D5a
_moduso-de_ : Ω → Ω → Prop
x moduso-de y = x ≢₁ y ∧ x ⊆ y ∧ x konc-per y

-- 1D5b
moduso : Ω → Prop
moduso x = ∃₁[ y ∈ Ω ] subst y ∧ x moduso-de y

-- 1D6
deo : Ω → Prop
deo x = subst x ∧ (∀₁[ y ∈ Ω ] atr y ⇒ y atr-of x)

-- 1D7
lib : Ω → Prop
lib x = x ⊢ x ∧ ¬ (∃₁[ y ∈ Ω ] y ≢₁ x ∧ y ⊢ x)

nec : Ω → Prop
nec x = ∃₁[ y ∈ Ω ] y ≢₁ x ∧ y ⊢ x

-- 1D8
eterna : Ω → Prop
eterna x = □ (∃₁[ y ∈ Ω ] y ≡₁ x)

record Aksiomoj : Set₁ where
  field
    -- 1D1 estas, fakte, aksiomo.
    1D1 : [ ∀₁[ x ∈ Ω ]
        (x ⊢ x ∧ ¬ (∃₁[ y ∈ Ω ] y ≢₁ x ∧ y ⊢ x))
      ⇔ (□ (∃₁[ y ∈ Ω ] y ≡₁ x))
      ]
    1A1a : [ ∀₁[ x ∈ Ω ]
        x ⊆ x ∨ (∃₁[ y ∈ Ω ] y ≢₁ x ∧ x ⊆ y)
      ]
    -- "Intuiciista" versio de 1A1 (la du versioj estas ekvivalentaj laŭ
    -- klasika logiko).
    1A1c : [ ∀₁[ x ∈ Ω ]
        ¬ (¬ (x ⊆ x) ∧ ¬ (∃₁[ y ∈ Ω ] y ≢₁ x ∧ x ⊆ y))
      ]
    1A2 : [ ∀₁[ x ∈ Ω ]
        ¬ (∃₁[ y ∈ Ω ] y ≢₁ x ∧ x konc-per y)
      ⇔ x konc-per x
      ]
    1A3 : [ ∀₁[ x ∈ Ω ] ∀₁[ y ∈ Ω ]
        y ⊢ x ⇒ □ ((∃₁[ z ∈ Ω ] z ≡₁ y) ⇔ (∃₁[ z ∈ Ω ] z ≡₁ x))
      ]
    -- 1A4
    -- Memoru, 1A4 estas difino (v. alte).
    1A5 : [ ∀₁[ x ∈ Ω ] ∀₁[ y ∈ Ω ]
        ¬ (∃₁[ z ∈ Ω ] z kom-al x kaj y) ⇔ (¬ (x konc-per y) ∧ ¬ (y konc-per x))
      ]
    1A6 : [ ∀₁[ x ∈ Ω ]
        ideo x ⇒ (vera x ⇔ (∃₁[ y ∈ Ω ] y objekto x ∧ x ak y))
      ]
    -- 1A7 estas vera en klasika modala logiko.
    1A7 : [ ∀₁[ x ∈ Ω ]
        (◇ ¬ (∃₁[ y ∈ Ω ] y ≡₁ x))
      ⇔ (¬ □ (∃₁[ y ∈ Ω ] y ≡₁ x))
      ]
    --
    -- Pliaj aksiomoj (forigitaj de Spinoza, sed necesaj).
    1A8 : {x y : Ω} → [ x ⊆ y ⇒ x konc-per y ]
    1A9 : {x : Ω} → [ ∃₁[ y ∈ Ω ] y atr-of x ]

postulate aksiomoj : Aksiomoj
open Aksiomoj aksiomoj

--
-- Helpaj teoremoj
--

1H1 : {x : Ω} → [ subst x ⇔ x ⊆ x ]
1H1 w = proj₁ , λ x⊆x → x⊆x , 1A8 w x⊆x

1H2-lem : {P Q : Prop} → [ ¬ (¬ P ∧ ¬ Q) ⇒ ¬ Q ⇒ ¬ ¬ P ]
1H2-lem w ¬[¬P∧¬Q] ¬Q ¬P = ¬[¬P∧¬Q] (¬P , ¬Q)

1H2 : {x : Ω} → [ x konc-per x ⇒ ¬ ¬ (x ⊆ x) ]
1H2 {x} w x-kp-x = 1H2-lem w (1A1c w x) ¬∃y-x⊆y
  where
  ¬∃y-x⊆y : (¬ (∃₁[ y ∈ Ω ] y ≢₁ x ∧ x ⊆ y)) w
  ¬∃y-x⊆y (y , (y≢x , x⊆y)) =
    proj₂ (1A2 w x) x-kp-x (y , (y≢x , 1A8 w x⊆y))

1H3 : {x : Ω} → [ subst x ⇒ atr x ]
1H3 {x} w s-x = (x , ((((s-x , x⊆x) , x-kp-x) , x⊆x) , x-kp-x))
  where
  x⊆x = proj₁ s-x
  x-kp-x = proj₂ s-x

1H4-lem : {P Q : Prop} → [ (P ⇔ Q) ⇒ ¬ ¬ P ⇒ ¬ ¬ Q ]
1H4-lem w (P⇒Q , Q⇒P) ¬¬P ¬Q =
  ¬¬P λ P → ¬Q (P⇒Q P)

1H4 : {x : Ω} → [ ¬ ¬ (subst x) ⇔ ¬ ¬ (x konc-per x) ]
1H4 {x} w = ltr , rtl
  where
  ltr : (¬ ¬ (subst x) ⇒ ¬ ¬ (x konc-per x)) w
  ltr ¬¬subst-x ¬x-kp-x =
    ¬¬subst-x λ subst-x → ¬x-kp-x (proj₂ subst-x)
  rtl : (¬ ¬ (x konc-per x) ⇒ ¬ ¬ (subst x)) w
  rtl ¬¬x-kp-x =
    ¬¬x-kp-x ?

--1H5 : {x : Ω} → [ subst x ∨ moduso x ]
--1H5 w = ?

--
-- Propozicioj
--

1P1 : {x y : Ω} → [ x moduso-de y ∧ subst y ⇒ x ⊆ y ∧ y ⊆ y ]
1P1 _ (xmy , substy) = x⊆y , y⊆y
  where
  x⊆y = proj₂ (proj₁ xmy)
  y⊆y = proj₁ substy

≡-sym : ∀ {l}{A : Set l}(x y : A) → x ≡ y → y ≡ x
≡-sym x .x (_≡_.refl) = _≡_.refl

≢-sym : ∀ {l}{A : Set l}(x y : A) → x ≢ y → y ≢ x
≢-sym x y x≢y y≡x = x≢y (≡-sym y x y≡x)

1P2 : {x y : Ω} → [ subst x ∧ subst y ∧ y ≢₁ x
  ⇒ ¬ (∃₁[ z ∈ Ω ] z kom-al x kaj y) ]
1P2 {x} {y} w ((substx , substy) , y≢x) =
  let
    x-kp-x = proj₂ substx
    y-kp-y = proj₂ substy
    ¬x-kp-≢ = proj₂ (1A2 w x) x-kp-x
    ¬y-kp-≢ = proj₂ (1A2 w y) y-kp-y
    ¬x-kp-y x-kp-y = ¬x-kp-≢ (y , (y≢x , x-kp-y))
    ¬y-kp-x y-kp-x = ¬y-kp-≢ (x , (≢-sym y x y≢x , y-kp-x))
  in
  proj₂ (1A5 w x y) (¬x-kp-y , ¬y-kp-x)

1P3 : {x y : Ω} → [ ¬ (∃₁[ z ∈ Ω ] z kom-al x kaj y) ⇒ ¬ (y ⊢ x) ∧ ¬ (x ⊢ y) ]
1P3 {x} {y} w = proj₁ (1A5 w x y)

1P4 : {x y : Ω} → [
    (x ≢₁ y)
  ⇒ (∃₁[ z ∈ Ω ] ∃₁[ z' ∈ Ω ] z atr-of x ∧ z' atr-of y ∧ z ≢₁ z')
    ∨ (∃₁[ z ∈ Ω ] z atr-of x ∧ z ≡₁ x ∧ moduso y)
    ∨ (∃₁[ z' ∈ Ω ] z' atr-of y ∧ z' ≡₁ y ∧ moduso x)
    ∨ (moduso x ∧ moduso y)
  ]
1P4 = ?
