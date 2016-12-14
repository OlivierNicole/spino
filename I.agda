-- Etiko
-- Parto I

--
-- Bazaj difinoj
--

data Bool : Set where
  true : Bool
  false : Bool

record True : Set where
data False : Set where

data _≡_ : {A : Set} → A → A → Set where
  refl : {A : Set}{x : A} → x ≡ x

data _≢_ : {A : Set} → A → A → Set where
  neq : {A : Set}{x y : A}{p : x ≡ y → False} → x ≢ y

data _∨_ : Set → Set → Set where
  inl : {A B : Set} → A → A ∨ B
  inr : {A B : Set} → B → A ∨ B

data _∧_ : Set → Set → Set where
  and : {A B : Set} → A → B → A ∧ B

data _⊕_ : Set → Set → Set where
  inl : {A B : Set} → A → (B → False) → A ⊕ B
  inr : {A B : Set} → (A → False) → B → A ⊕ B

--
-- Implicaj konceptoj
--

-- estas kaŭzo de
data _⇒_ : {A : Set} → A → A → Set where
  ⇒-ax : {A : Set}{x y : A} → x ⇒ y

-- ekzisto
data ekzistas : {A : Set} → A → Set where
  ekz-ax : {A : Set}{x : A} → ekzistas x

-- esti en, sin koncepti per
data _⊆_ : {A : Set} → A → A → Set where
  ⊆-ax : {A : Set}{x y : A} → x ⊆ y

data _⊊_ : {A : Set} → A → A → Set where
  not-⊆ : {A : Set}{x y : A}{p : x ⊆ y → False} → x ⊊ y

--
-- Difinoj
--

-- 1D1
{-
  Per _kaŭzo de si_ mi komprenas tion, de kio la esto envolvas la ekzisto, aŭ
  tio, de kio la naturo sin konceptas nur kiel ekzistanta.
-}
1d1 : ∀ {x} → x ⇒ x → ekzistas x
1d1 ⇒-ax = ekz-ax

-- 1D2
{-
  Ian aĵon oni diras _finia en sia ĝenro_ kiam ĝin randas alia aĵo de sama
  naturo. Ekzemple, ian korpon oni diras finia aĵo, ĉar ni ĉiam konceptas alian,
  pli grandan korpon ; same, ia pensaĵo estas randata de alia pensaĵo ; sed
  korpo ne estas randata de pensaĵo, nek pensaĵo de korpo.
-}
data finia : {A : Set} → A → Set where
  1d2 : {A : Set}{x y : A} → x ⊆ y → finia x

-- 1D3
{-
  Per _substanco_ mi komprenas tion, kio estas en si kaj konceptiĝas per si,
  t. e. tio, de kio la koncepto oni povas formi sen la koncepto de alia aĵo.
-}
data substanco : {A : Set} → A → Set where
  1d3 : {A : Set}{x y : A} → (x ⊆ y → x ≡ x) → substanco x

-- 1D4
{-
  Per _atributo_ mi komprenas tion, kion la racio konceptas en la substanco,
  kiel estanta la esenco de ĝi.
-}
-- ???

-- 1D5
{-
  Per _moduso_ mi komprenas la afekcioj de la substanco, aŭ tio, kio estas en
  io alia kaj konceptita de tio.
-}
data moduso : {A : Set} → A → Set where
  1d5 : {A : Set}{x y : A} → x ⊆ y → x ≢ y → moduso x

-- 1D6
{-
  Per _Deo_ mi komprenas estulo tute malfinia, t. e. substanco kunfarita de
  malfinio de atributoj, ĉiu esprimanta eterna kaj malfinia esenco.
-}
-- NOT SURE
data deo : {A : Set} → A → Set where
  1d6 : {A : Set}{x : A} → (finia x → False) → deo x

-- 1D7
{-
  Ia aĵo estas _libera_, kiam ĝi ekzistas per la sola neceso de sia naturo, kaj
  estas igita agi nur de si mem ; …
-}
data libera : {A : Set} → A → Set where
  1d7 : {A : Set}{x y : A} → (x ⇒ y → x ≡ y) → libera x

-- 1D8
{-
  Per _eterneco_, mi komprenas ekzisto mem, kiel konceptita necese rezultanta de
  la sola difino de la eterna aĵo.
-}
-- ???

--
-- Aksiomoj
--

-- 1A1
{-
  Ĉio, kio estas, estas aŭ en si aŭ en io alia.
-}
-- ???

-- 1A2
{-
  Ia aĵo, kiu ne povas sin koncepti per io alia devas sin koncepti per si.
-}
1a2 : {A : Set}{x y : A} → (x ⊆ y → x ≡ y) → x ⊆ x
1a2 _ = ⊆-ax

-- 1A3
1a3 : {A : Set}{x y : A} → x ⇒ y → ekzistas x → ekzistas y
1a3 _ _ = ekz-ax

1a3' : {A : Set}{x y : A} → (x ⇒ y → ekzistas x → False) →
  x ⇒ y → ekzistas y → False
1a3' f p _ = f p ekz-ax

-- 1A4
{-
  La konado de la efiko dependas de la konado de la kaŭzo, kaj involvas ĝin.
-}
-- ???

-- 1A5 to 1A7 : ???

-- 1P1
--1p1 : {A : Set}{x y : A} → substanco x → moduso y → y ⊆ x
-- ???

-- 1P2
-- Ĉi tie mi interpretas "malsamaj atributoj" kiel "x ≢ y".
--1p2 : ∀ {A x y} → substanco x → substanco y → x ≢ y → (x ⊊ y) ∧ (y ⊊ x)
