-- Etiko, Parto I.

open import Logic.Modal.S5
open import Data.Product using ( _,_ )

--
-- Bazaj predikatoj.
--

unuloka-pred : Set₁
unuloka-pred = {A : Set}(x : A) → Set

-- atr x : x estas atributo
data atr : unuloka-pred where
  atr-ax : {A : Set}(x : A) → atr x

-- lib x : x estas libera
data lib : unuloka-pred where
  lib-ax : {A : Set}(x : A) → lib x

-- dez x : x estas (instanco de) deziro
data dez : unuloka-pred where
  dez-ax : {A : Set}(x : A) → dez x

-- eterna x : x estas eterna
data eterna : unuloka-pred where
  eterna-ax : {A : Set}(x : A) → eterna x

duloka-pred : Set₁
duloka-pred = {A : Set}(x y : A) → Set

-- x ⊆ y : x estas en y
data _⊆_ : duloka-pred where
  ⊆-ax : {A : Set}(x y : A) → x ⊆ y

-- x ≤ y : x konceptiĝas per y
data _≤_ : duloka-pred where
  ≤-ax : {A : Set}(x y : A) → x ≤ y

-- x ⊢ y : x kaŭzas y
data _⊢_ : duloka-pred where
  ⊢-ax : {A : Set}(x y : A) → x ⊢ y
