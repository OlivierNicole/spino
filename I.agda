-- Etiko, Parto I.
module I where

import Logic.Modal.S5
open import Data.Product
open import Data.Sum
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_ ; refl)
open import Function

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
    1A1 : [ ∀₁[ x ∈ Ω ]
        x ⊆ x ∨ (∃₁[ y ∈ Ω ] y ≢₁ x ∧ x ⊆ y)
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
    1A11 : {x y : Ω} → [ subst x ⇒ x ≤ y ⇒ subst y ]
    1A12 : {x : Ω} → [ (∃₁[ y ∈ Ω ] x moduso-de y) ⇒ moduso x ]

postulate aksiomoj : Aksiomoj
open Aksiomoj aksiomoj

open Classical

--
-- Agda helpaĵoj
--

infixl 0 _⦊_
_⦊_ : ∀ {a b} {A : Set a} {B : A → Set b} →
  (x : A) → ((x : A) → B x) → B x
x ⦊ f = f x

≡-sym : ∀ {l} {A : Set l} {x y : A} → x ≡ y → y ≡ x
≡-sym refl = refl

≡-trans : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡-trans refl refl = refl

≢-sym : ∀ {l} {A : Set l} {x y : A} → x ≢ y → y ≢ x
≢-sym x≢y y≡x = x≢y (≡-sym y≡x)

--
-- Helpaj teoremoj
--

1H1 : {x : Ω} → [ subst x ⇔ x ⊆ x ]
1H1 = proj₁ , λ x⊆x → x⊆x , 1A8 x⊆x

1H2 : {x : Ω} → [ x konc-per x ⇒ x ⊆ x ]
1H2 {x} x-kp-x =
  let ¬∃y = proj₂ (1A2 x) x-kp-x in
  neg-inj₂
    {P = x ⊆ x}
    {Q = ∃₁[ y ∈ Ω ] y ≢₁ x ∧ x ⊆ y}
    (1A1 x) λ
    { (y , (y≢x , x⊆y)) → ¬∃y (y , (y≢x , (1A8 x⊆y)))
    }

1H3 : {x : Ω} → [ subst x ⇒ atr x ]
1H3 {x} s-x = (x , s-x , x⊆x , x-kp-x , x⊆x , x-kp-x)
  where
  x⊆x = proj₁ s-x
  x-kp-x = proj₂ s-x

1H4-lem : {P Q : Prop} → [ (P ⇔ Q) ⇒ ¬ ¬ P ⇒ ¬ ¬ Q ]
1H4-lem (P⇒Q , Q⇒P) ¬¬P ¬Q =
  ¬¬P λ P → ¬Q (P⇒Q P)

1H4 : {x : Ω} → [ subst x ⇔ x konc-per x ]
1H4 {x} {w = w} = ltr , rtl
  where
  ltr : (subst x ⇒ x konc-per x) w
  ltr = proj₂
  rtl : (x konc-per x ⇒ subst x) w
  rtl x-kp-x =
    1H2 x-kp-x , x-kp-x

1H5 : {x : Ω} → [ subst x ∨ moduso x ]
1H5 {x} {w} with 1A1 x
... | (inj₁ x⊆x) = x⊆x , 1A8 x⊆x ⦊ inj₁
... | (inj₂ (y , y≢x , x⊆y)) =
  y , ≢-sym y≢x , x⊆y , 1A8 x⊆y ⦊ 1A12 ⦊ inj₂

1H6 : {x : Ω} → [ ¬ (subst x ∧ moduso x) ]
1H6 {x} ((_ , x-kp-x) , (y , _ , x≢y , _ , x-kp-y)) =
  y , ≢-sym x≢y , x-kp-y ⦊ proj₂ (1A2 x) x-kp-x

1H7 : {x y : Ω} → [ x atr-of y ∧ subst y ⇒ x ≡₁ y ]
1H7 {x} {y} {w} ((atr-x , y-kp-x) , (_ , y-kp-y)) =
  dne {w = w} λ x≢y → x , x≢y , y-kp-x ⦊ proj₂ (1A2 y) y-kp-y

--
-- Propozicioj
--

1P1 : {x y : Ω} → [ x moduso-de y ∧ subst y ⇒ x ⊆ y ∧ y ⊆ y ]
1P1 (xmy , substy) = x⊆y , y⊆y
  where
  x⊆y = proj₁ (proj₂ xmy)
  y⊆y = proj₁ substy

1P2 : {x y : Ω} → [ subst x ∧ subst y ∧ x ≢₁ y
  ⇒ ¬ (∃₁[ z ∈ Ω ] z kom-al x kaj y) ]
1P2 {x} {y} (substx , substy , x≢y) =
  let
    x-kp-x = proj₂ substx
    y-kp-y = proj₂ substy
    ¬x-kp-≢ = proj₂ (1A2 x) x-kp-x
    ¬y-kp-≢ = proj₂ (1A2 y) y-kp-y
    ¬x-kp-y x-kp-y = ¬x-kp-≢ (y , (≢-sym x≢y , x-kp-y))
    ¬y-kp-x y-kp-x = ¬y-kp-≢ (x , (x≢y , y-kp-x))
  in
  proj₂ (1A5 x y) (¬x-kp-y , ¬y-kp-x)

1P3 : {x y : Ω} → [ ¬ (∃₁[ z ∈ Ω ] z kom-al x kaj y) ⇒ ¬ (x ⊢ y) ∧ ¬ (y ⊢ x) ]
1P3 {x} {y} prel = prel ⦊ proj₁ (1A5 x y) ⦊ λ
  { (¬x-kp-y , ¬y-kp-x) → ¬y-kp-x , ¬x-kp-y
  }

1P4 : {x y : Ω} → [
    (x ≢₁ y) ⇒ (∃₁[ z ∈ Ω ] ∃₁[ z' ∈ Ω ]
      (z atr-of x ∧ z' atr-of y ∧ z ≢₁ z')
    ∨ (z atr-of x ∧ z ≡₁ x ∧ moduso y)
    ∨ (z' atr-of y ∧ z' ≡₁ y ∧ moduso x)
    ∨ (moduso x ∧ moduso y)
    )
  ]
1P4 {x} {y} {w} x≢y with 1A9 {x} | 1A9 {y}
... | (z , z-atr-x) | (z' , z'-atr-y) =
  (z , z' , 1P4')
  where
  1P4' : (
      (z atr-of x ∧ z' atr-of y ∧ z ≢₁ z')
    ∨ (z atr-of x ∧ z ≡₁ x ∧ moduso y)
    ∨ (z' atr-of y ∧ z' ≡₁ y ∧ moduso x)
    ∨ (moduso x ∧ moduso y)
    ) w
  1P4' with 1H5 {x} | 1H5 {y}
  ... | inj₁ s-x | inj₁ s-y =
    z-atr-x , z'-atr-y , z≢z' ⦊ inj₁ ⦊ inj₁ ⦊ inj₁
    where
    z≢z' : z ≢ z'
    z≢z' = λ z≡z' →
      let
        z≡x = 1H7 {z} {x} (z-atr-x , s-x)
        z'≡y = 1H7 {z'} {y} (z'-atr-y , s-y)
      in
      x≢y (≡-trans (≡-trans (≡-sym z≡x) z≡z') z'≡y)
  ... | inj₁ s-x | inj₂ m-y =
    z-atr-x , 1H7 {z} {x} (z-atr-x , s-x) , m-y ⦊ inj₂ ⦊ inj₁ ⦊ inj₁
  ... | inj₂ m-x | inj₁ s-y =
    z'-atr-y , 1H7 {z'} {y} (z'-atr-y , s-y) , m-x ⦊ inj₂ ⦊ inj₁
  ... | inj₂ m-x | inj₂ m-y =
    m-x , m-y ⦊ inj₂

1P5 : {x y : Ω} → [ subst x ∧ subst y ∧ x ≢₁ y
  ⇒ ¬ (∃₁[ w ∈ Ω ] w atr-of x ∧ w atr-of y) ]
1P5 (s-x , s-y , x≢y) (w , w-atr-x , w-atr-y) =
  ≡-trans
    (≡-sym (1H7 (w-atr-x , s-x)))
    (1H7 (w-atr-y , s-y))
  ⦊ x≢y

1P6 : {x y : Ω} → [ subst x ∧ subst y ∧ x ≢₁ y ⇒ ¬ (x ⊢ y) ∧ ¬ (y ⊢ x) ]
1P6 prel = 1P2 prel ⦊ 1P3

-- En 1P6c mi uzas 1D3, 1A4 (kiel difino) kaj 1A2. Spinoza nur citas 1D3 kaj
-- 1A4.
1P6c : {x : Ω} → [ subst x ⇒ ¬ (∃₁[ y ∈ Ω ] y ≢₁ x ∧ y ⊢ x) ]
1P6c {x} s-x = proj₂ s-x ⦊ proj₂ (1A2 x)

1P7 : {x : Ω} → [ subst x ⇒ □ (∃₁[ y ∈ Ω ] y ≡₁ x) ]
1P7 {x} s-x = proj₂ s-x , 1P6c s-x ⦊ proj₁ (1D1 x)

1P8 : {x : Ω} → [ subst x ⇒ ¬ (finia x) ]
1P8 {x} s-x (y , y≢x , x≤y , same-atr) with 1A9 {x}
... | (a , a-atr-x) =
  1P5 (s-x , 1A11 s-x x≤y , ≢-sym y≢x)
    (a , a-atr-x , proj₁ (same-atr a) a-atr-x)
