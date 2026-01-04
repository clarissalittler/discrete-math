{-# OPTIONS --type-in-type #-}

module Week02_Functions where

open import Common

-- Function composition
_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(g ∘ f) x = g (f x)

infixr 9 _∘_

-- Also keep the named version for clarity
Compose : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
Compose g f = g ∘ f

-- Identity function
id : {A : Set} -> A -> A
id x = x

-- Constant function
const : {A B : Set} -> A -> B -> A
const a _ = a

-- Function properties
Injective : {A B : Set} -> (A -> B) -> Set
Injective {A} f = (x y : A) -> Eq (f x) (f y) -> Eq x y

Surjective : {A B : Set} -> (A -> B) -> Set
Surjective {A} {B} f = (y : B) -> Sigma A (\x -> Eq (f x) y)

Bijective : {A B : Set} -> (A -> B) -> Set
Bijective f = Pair (Injective f) (Surjective f)

-- Inverses
LeftInverse : {A B : Set} -> (B -> A) -> (A -> B) -> Set
LeftInverse {A} g f = (x : A) -> Eq (g (f x)) x

RightInverse : {A B : Set} -> (B -> A) -> (A -> B) -> Set
RightInverse {B = B} g f = (y : B) -> Eq (f (g y)) y

TwoSidedInverse : {A B : Set} -> (B -> A) -> (A -> B) -> Set
TwoSidedInverse g f = Pair (LeftInverse g f) (RightInverse g f)

-- Identity function properties
idInjective : {A : Set} -> Injective (id {A})
idInjective x y eq = eq

idSurjective : {A : Set} -> Surjective (id {A})
idSurjective y = sigma y refl

idBijective : {A : Set} -> Bijective (id {A})
idBijective = pair idInjective idSurjective

-- Composition properties
composeAssoc : {A B C D : Set} {f : A -> B} {g : B -> C} {h : C -> D} ->
  (x : A) -> Eq (((h ∘ g) ∘ f) x) ((h ∘ (g ∘ f)) x)
composeAssoc x = refl

composeIdLeft : {A B : Set} {f : A -> B} -> (x : A) -> Eq ((id ∘ f) x) (f x)
composeIdLeft x = refl

composeIdRight : {A B : Set} {f : A -> B} -> (x : A) -> Eq ((f ∘ id) x) (f x)
composeIdRight x = refl

-- Left inverse implies injective
leftInverseInjective : {A B : Set} {f : A -> B} {g : B -> A} ->
  LeftInverse g f -> Injective f
leftInverseInjective {g = g} left x y fx=fy =
  trans (sym (left x)) (trans (cong g fx=fy) (left y))

-- Right inverse implies surjective
rightInverseSurjective : {A B : Set} {f : A -> B} {g : B -> A} ->
  RightInverse g f -> Surjective f
rightInverseSurjective {g = g} right y = sigma (g y) (right y)

-- Two-sided inverse implies bijective
twoSidedInverseBijective : {A B : Set} {f : A -> B} {g : B -> A} ->
  TwoSidedInverse g f -> Bijective f
twoSidedInverseBijective {f = f} {g = g} (pair left right) =
  pair (leftInverseInjective {f = f} {g = g} left)
       (rightInverseSurjective {f = f} {g = g} right)

-- Composition of injective functions
composeInjective : {A B C : Set} {f : A -> B} {g : B -> C} ->
  Injective f -> Injective g -> Injective (g ∘ f)
composeInjective {f = f} {g = g} injF injG x y eq =
  injF x y (injG (f x) (f y) eq)

-- Composition of surjective functions
composeSurjective : {A B C : Set} {f : A -> B} {g : B -> C} ->
  Surjective f -> Surjective g -> Surjective (g ∘ f)
composeSurjective {f = f} {g = g} surF surG z with surG z
... | sigma y gy with surF y
... | sigma x fx = sigma x (trans (cong g fx) gy)

-- Composition of bijective functions
composeBijective : {A B C : Set} {f : A -> B} {g : B -> C} ->
  Bijective f -> Bijective g -> Bijective (g ∘ f)
composeBijective (pair injF surF) (pair injG surG) =
  pair (composeInjective injF injG) (composeSurjective surF surG)

-- If g ∘ f is injective, then f is injective
composeInjectiveLeft : {A B C : Set} {f : A -> B} {g : B -> C} ->
  Injective (g ∘ f) -> Injective f
composeInjectiveLeft {g = g} injGF x y fx=fy = injGF x y (cong g fx=fy)

-- If g ∘ f is surjective, then g is surjective
composeSurjectiveRight : {A B C : Set} {f : A -> B} {g : B -> C} ->
  Surjective (g ∘ f) -> Surjective g
composeSurjectiveRight {f = f} surGF z with surGF z
... | sigma x eq = sigma (f x) eq

-- Flip: swap arguments of a two-argument function
flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f b a = f a b

-- Application operator
_$_ : {A B : Set} -> (A -> B) -> A -> B
f $ x = f x

infixr 0 _$_

-- Currying and uncurrying
curry : {A B C : Set} -> (Pair A B -> C) -> A -> B -> C
curry f a b = f (pair a b)

uncurry : {A B C : Set} -> (A -> B -> C) -> Pair A B -> C
uncurry f (pair a b) = f a b

-- Preimage/inverse image of a predicate
Preimage : {A B : Set} -> (A -> B) -> Pred B -> Pred A
Preimage f P x = P (f x)

-- Direct image of a predicate
Image : {A B : Set} -> (A -> B) -> Pred A -> Pred B
Image {A} f P y = Sigma A (\x -> Pair (P x) (Eq (f x) y))

-- Cardinality comparison via injections and surjections
_≲_ : Set -> Set -> Set
A ≲ B = Sigma (A -> B) Injective

_≳_ : Set -> Set -> Set
A ≳ B = Sigma (A -> B) Surjective

-- Isomorphism between sets
record _≅_ (A B : Set) : Set where
  field
    to : A -> B
    from : B -> A
    leftInv : LeftInverse from to
    rightInv : RightInverse from to

-- Isomorphism implies bijection
isoToBijective : {A B : Set} -> A ≅ B -> Sigma (A -> B) Bijective
isoToBijective iso = sigma (_≅_.to iso)
  (twoSidedInverseBijective (pair (_≅_.leftInv iso) (_≅_.rightInv iso)))

-- Reflexivity of isomorphism
isoRefl : {A : Set} -> A ≅ A
isoRefl = record { to = id ; from = id ; leftInv = \_ -> refl ; rightInv = \_ -> refl }

-- Symmetry of isomorphism
isoSym : {A B : Set} -> A ≅ B -> B ≅ A
isoSym iso = record
  { to = _≅_.from iso
  ; from = _≅_.to iso
  ; leftInv = _≅_.rightInv iso
  ; rightInv = _≅_.leftInv iso
  }

-- Transitivity of isomorphism
isoTrans : {A B C : Set} -> A ≅ B -> B ≅ C -> A ≅ C
isoTrans ab bc = record
  { to = _≅_.to bc ∘ _≅_.to ab
  ; from = _≅_.from ab ∘ _≅_.from bc
  ; leftInv = \x -> trans (cong (_≅_.from ab) (_≅_.leftInv bc (_≅_.to ab x)))
                          (_≅_.leftInv ab x)
  ; rightInv = \y -> trans (cong (_≅_.to bc) (_≅_.rightInv ab (_≅_.from bc y)))
                           (_≅_.rightInv bc y)
  }
