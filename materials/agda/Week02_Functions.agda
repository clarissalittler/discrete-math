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

-- ============================================
-- STANDARD ISOMORPHISMS
-- ============================================

-- Currying isomorphism: (A × B → C) ≅ (A → B → C)
-- Note: Full isomorphism requires function extensionality
-- We demonstrate the pointwise version instead

curryUncurryPointwise : {A B C : Set} (f : Pair A B -> C) (p : Pair A B) ->
  Eq (uncurry (curry f) p) (f p)
curryUncurryPointwise f (pair a b) = refl

uncurryCurryPointwise : {A B C : Set} (f : A -> B -> C) (a : A) (b : B) ->
  Eq (curry (uncurry f) a b) (f a b)
uncurryCurryPointwise f a b = refl

-- With function extensionality (postulated), we could prove the full isomorphism
postulate
  funext : {A : Set} {B : A -> Set} {f g : (x : A) -> B x} ->
    ((x : A) -> Eq (f x) (g x)) -> Eq f g

curryIso : {A B C : Set} -> (Pair A B -> C) ≅ (A -> B -> C)
curryIso = record
  { to = curry
  ; from = uncurry
  ; leftInv = \f -> funext (\{ (pair a b) -> refl })
  ; rightInv = \f -> funext (\a -> funext (\b -> refl))
  }

-- Product commutativity: A × B ≅ B × A
prodCommIso : {A B : Set} -> Pair A B ≅ Pair B A
prodCommIso = record
  { to = \{ (pair a b) -> pair b a }
  ; from = \{ (pair b a) -> pair a b }
  ; leftInv = \{ (pair a b) -> refl }
  ; rightInv = \{ (pair b a) -> refl }
  }

-- Product associativity: (A × B) × C ≅ A × (B × C)
prodAssocIso : {A B C : Set} -> Pair (Pair A B) C ≅ Pair A (Pair B C)
prodAssocIso = record
  { to = \{ (pair (pair a b) c) -> pair a (pair b c) }
  ; from = \{ (pair a (pair b c)) -> pair (pair a b) c }
  ; leftInv = \{ (pair (pair a b) c) -> refl }
  ; rightInv = \{ (pair a (pair b c)) -> refl }
  }

-- Sum commutativity: A + B ≅ B + A
sumCommIso : {A B : Set} -> Sum A B ≅ Sum B A
sumCommIso = record
  { to = \{ (inl a) -> inr a ; (inr b) -> inl b }
  ; from = \{ (inl b) -> inr b ; (inr a) -> inl a }
  ; leftInv = \{ (inl a) -> refl ; (inr b) -> refl }
  ; rightInv = \{ (inl b) -> refl ; (inr a) -> refl }
  }

-- Sum associativity: (A + B) + C ≅ A + (B + C)
sumAssocIso : {A B C : Set} -> Sum (Sum A B) C ≅ Sum A (Sum B C)
sumAssocIso = record
  { to = \{ (inl (inl a)) -> inl a ; (inl (inr b)) -> inr (inl b) ; (inr c) -> inr (inr c) }
  ; from = \{ (inl a) -> inl (inl a) ; (inr (inl b)) -> inl (inr b) ; (inr (inr c)) -> inr c }
  ; leftInv = \{ (inl (inl a)) -> refl ; (inl (inr b)) -> refl ; (inr c) -> refl }
  ; rightInv = \{ (inl a) -> refl ; (inr (inl b)) -> refl ; (inr (inr c)) -> refl }
  }

-- Unit is identity for product: Unit × A ≅ A
unitProdIso : {A : Set} -> Pair Unit A ≅ A
unitProdIso = record
  { to = \{ (pair unit a) -> a }
  ; from = \a -> pair unit a
  ; leftInv = \{ (pair unit a) -> refl }
  ; rightInv = \a -> refl
  }

-- Empty is zero for sum: Empty + A ≅ A
emptySumIso : {A : Set} -> Sum Empty A ≅ A
emptySumIso = record
  { to = \{ (inl ()) ; (inr a) -> a }
  ; from = inr
  ; leftInv = \{ (inl ()) ; (inr a) -> refl }
  ; rightInv = \a -> refl
  }

-- Empty is zero for product: Empty × A ≅ Empty
emptyProdIso : {A : Set} -> Pair Empty A ≅ Empty
emptyProdIso = record
  { to = \{ (pair () a) }
  ; from = absurd
  ; leftInv = \{ (pair () a) }
  ; rightInv = \()
  }

-- Distributivity: A × (B + C) ≅ (A × B) + (A × C)
distribIso : {A B C : Set} -> Pair A (Sum B C) ≅ Sum (Pair A B) (Pair A C)
distribIso = record
  { to = \{ (pair a (inl b)) -> inl (pair a b) ; (pair a (inr c)) -> inr (pair a c) }
  ; from = \{ (inl (pair a b)) -> pair a (inl b) ; (inr (pair a c)) -> pair a (inr c) }
  ; leftInv = \{ (pair a (inl b)) -> refl ; (pair a (inr c)) -> refl }
  ; rightInv = \{ (inl (pair a b)) -> refl ; (inr (pair a c)) -> refl }
  }

-- ============================================
-- CATEGORICAL PERSPECTIVE
-- ============================================

{-
  Functions form a CATEGORY!

  Objects: Sets (types)
  Morphisms: Functions between sets
  Identity: id function
  Composition: ∘

  The laws are satisfied:
  1. id ∘ f = f             (left identity)
  2. f ∘ id = f             (right identity)
  3. (h ∘ g) ∘ f = h ∘ (g ∘ f)  (associativity)

  We proved these above as composeIdLeft, composeIdRight, composeAssoc!
-}

-- Functor laws for map on lists
-- A functor F satisfies:
--   F(id) = id
--   F(g ∘ f) = F(g) ∘ F(f)

mapId : {A : Set} (xs : List A) -> Eq (map id xs) xs
mapId [] = refl
mapId (x :: xs) = cong (x ::_) (mapId xs)

mapCompose : {A B C : Set} (g : B -> C) (f : A -> B) (xs : List A) ->
  Eq (map (g ∘ f) xs) (map g (map f xs))
mapCompose g f [] = refl
mapCompose g f (x :: xs) = cong (g (f x) ::_) (mapCompose g f xs)

-- ============================================
-- EXERCISES
-- ============================================

{-
  EXERCISE 1: Prove that id is a two-sided inverse for itself
-}
exercise-idInverse : {A : Set} -> TwoSidedInverse (id {A}) id
exercise-idInverse = pair (\x -> refl) (\x -> refl)

{-
  EXERCISE 2: Prove that the successor function on Nat is injective
-}
exercise-succInjective : Injective succ
exercise-succInjective x y eq with eq
... | refl = refl

{-
  EXERCISE 3: Prove that const is NOT injective (in general)
  Hint: Find a counterexample by constructing two different inputs
  that map to the same output
-}
-- const-not-injective : Not (Injective (const {Nat} {Bool} zero))
-- Proof would require that zero = succ zero from const zero true = const zero false

{-
  EXERCISE 4: Prove that if f has a left inverse, f is injective
  (This is leftInverseInjective, try proving it yourself!)
-}
exercise-leftInvInj : {A B : Set} {f : A -> B} {g : B -> A} ->
  LeftInverse g f -> Injective f
exercise-leftInvInj {g = g} left x y fx=fy =
  trans (sym (left x)) (trans (cong g fx=fy) (left y))

{-
  EXERCISE 5: Show that preimage preserves subset
  If P ⊆ Q, then f⁻¹(P) ⊆ f⁻¹(Q)
-}
open import Week01_SetTheory using (_⊆_)

exercise-preimageSubset : {A B : Set} (f : A -> B) {P Q : Pred B} ->
  P ⊆ Q -> Preimage f P ⊆ Preimage f Q
exercise-preimageSubset f pq x pfx = pq (f x) pfx

{-
  EXERCISE 6: Prove that composition of left inverses is a left inverse
  If g is left inverse of f, and g' is left inverse of h,
  then g ∘ g' is left inverse of h ∘ f
-}
postulate
  exercise-composeLeftInverse : {A B C : Set} {f : A -> B} {g : B -> A}
    {h : B -> C} {g' : C -> B} ->
    LeftInverse g f -> LeftInverse g' h ->
    LeftInverse (g ∘ g') (h ∘ f)

{-
  EXERCISE 7: Show that flip is an involution: flip (flip f) = f
-}
exercise-flipInvolution : {A B C : Set} (f : A -> B -> C) (a : A) (b : B) ->
  Eq (flip (flip f) a b) (f a b)
exercise-flipInvolution f a b = refl

{-
  EXERCISE 8: Prove that uncurry ∘ curry = id (part of currying isomorphism)
-}
exercise-uncurryCurry : {A B C : Set} (f : Pair A B -> C) (p : Pair A B) ->
  Eq (uncurry (curry f) p) (f p)
exercise-uncurryCurry f (pair a b) = refl

{-
  EXERCISE 9: Define and prove Maybe is a functor
-}
mapMaybe : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe f nothing = nothing
mapMaybe f (just x) = just (f x)

exercise-mapMaybeId : {A : Set} (m : Maybe A) -> Eq (mapMaybe id m) m
exercise-mapMaybeId nothing = refl
exercise-mapMaybeId (just x) = refl

exercise-mapMaybeCompose : {A B C : Set} (g : B -> C) (f : A -> B) (m : Maybe A) ->
  Eq (mapMaybe (g ∘ f) m) (mapMaybe g (mapMaybe f m))
exercise-mapMaybeCompose g f nothing = refl
exercise-mapMaybeCompose g f (just x) = refl

{-
  EXERCISE 10 (Challenge): Prove Cantor's theorem in type theory
  There is no surjection from A to (A -> Bool)
-}
postulate
  exercise-cantor : {A : Set} (f : A -> (A -> Bool)) -> Not (Surjective f)
  -- The actual proof uses diagonalization, similar to the classic set-theoretic proof
  -- Key idea: the function d(x) = not (f x x) cannot be in the image of f
