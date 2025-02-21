module FirstAgda where

-- Define the unit type (⊤), which has exactly one constructor 'tt'
data ⊤ : Set where
  tt : ⊤

-- If we have a function from ⊤ to any type A, we can get an element of A
-- by applying the function to tt
lemma-1 : {A : Set} -> (⊤ -> A) -> A
lemma-1 p = p tt

-- Define the empty type (⊥), which has no constructors
data ⊥ : Set where

-- From a value of type ⊥, we can derive anything (ex falso quodlibet)
-- The () pattern indicates there are no possible values to match
lemma-2 : {A : Set} -> ⊥ -> A
lemma-2 ()

-- Define natural numbers inductively with zero and successor
data Nat : Set where
  z : Nat            -- Zero
  s : Nat -> Nat    -- Successor function

-- Define addition on natural numbers
_+_ : Nat -> Nat -> Nat
z + n2 = n2                 -- 0 + n = n
s n1 + n2 = s (n1 + n2)    -- (1 + n) + m = 1 + (n + m)

-- Define vectors (lists with length information in the type)
data Vec (A : Set) : Nat -> Set where
  empty : Vec A z                                    -- Empty vector
  cons  : ∀ {n : Nat} -> A -> Vec A n -> Vec A (s n) -- Add element to vector

-- Get the first element of a non-empty vector
pop : {A : Set} {n : Nat} -> Vec A (s n) -> A
pop (cons x v) = x

-- Define propositional equality
data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a    -- Reflexivity is the only constructor

-- Prove symmetry of equality
≡-sym : ∀ {A : Set} {a1 a2 : A} -> (a1 ≡ a2) -> (a2 ≡ a1)
≡-sym refl = refl

-- Prove transitivity of equality
≡-trans : {A : Set} {a1 a2 a3 : A} -> (a1 ≡ a2) -> (a2 ≡ a3) -> a1 ≡ a3
≡-trans refl p23 = p23

-- Prove that functions preserve equality (congruence)
cong : {A B : Set} {a1 a2 : A}
  -> (f : A -> B) -> a1 ≡ a2 -> (f a1) ≡ (f a2)
cong f refl = refl

-- Prove that zero is left identity for addition
add-zero : (n : Nat) -> (z + n) ≡ n
add-zero n = refl

-- Prove that zero is right identity for addition (by induction)
add-zero-2 : (n : Nat) -> (n + z) ≡ n
add-zero-2 z = refl
add-zero-2 (s n) = cong s (add-zero-2 n)

-- Prove property about successor and left addition
add-succ-l : (n1 n2 : Nat) -> (s n1 + n2) ≡ s (n1 + n2)
add-succ-l n1 n2 = refl

-- Prove property about successor and right addition (by induction)
add-succ-r : (n1 n2 : Nat) -> (n1 + (s n2)) ≡ s (n1 + n2)
add-succ-r z n2 = refl
add-succ-r (s n1) n2 = cong s (add-succ-r n1 n2)

-- Prove commutativity of addition
+-commut : (n1 n2 : Nat) -> (n1 + n2) ≡ (n2 + n1)
-- Base case: 0 + n = n = n + 0
+-commut z n2 = ≡-trans (add-zero n2) (≡-sym (add-zero-2 n2))
-- Inductive case: (1 + n) + m = 1 + (n + m) = 1 + (m + n) = m + (1 + n)
+-commut (s n1) n2 = ≡-trans (add-succ-l n1 n2)
                    (≡-sym (≡-trans (add-succ-r n2 n1) (cong s (+-commut n2 n1))))

