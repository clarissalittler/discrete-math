{-# OPTIONS --type-in-type #-}

module Common where

data Unit : Set where
  unit : Unit

data Empty : Set where

absurd : {A : Set} -> Empty -> A
absurd ()

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

one : Nat
one = succ zero

_+_ : Nat -> Nat -> Nat
zero + n = n
succ m + n = succ (m + n)

_*_ : Nat -> Nat -> Nat
zero * n = zero
succ m * n = n + (m * n)

infixl 6 _+_
infixl 7 _*_

_-_ : Nat -> Nat -> Nat
n - zero = n
zero - succ m = zero
succ n - succ m = n - m

data Eq {A : Set} : A -> A -> Set where
  refl : {x : A} -> Eq x x

sym : {A : Set} {x y : A} -> Eq x y -> Eq y x
sym refl = refl

trans : {A : Set} {x y z : A} -> Eq x y -> Eq y z -> Eq x z
trans refl p = p

cong : {A B : Set} (f : A -> B) {x y : A} -> Eq x y -> Eq (f x) (f y)
cong f refl = refl

data Pair (A B : Set) : Set where
  pair : A -> B -> Pair A B

fst : {A B : Set} -> Pair A B -> A
fst (pair a b) = a

snd : {A B : Set} -> Pair A B -> B
snd (pair a b) = b

data Sum (A B : Set) : Set where
  inl : A -> Sum A B
  inr : B -> Sum A B

data Sigma (A : Set) (B : A -> Set) : Set where
  sigma : (x : A) -> B x -> Sigma A B

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

infixr 5 _::_

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 5 _++_

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr f z [] = z
foldr f z (x :: xs) = f x (foldr f z xs)

length : {A : Set} -> List A -> Nat
length [] = zero
length (_ :: xs) = succ (length xs)

sum : List Nat -> Nat
sum [] = zero
sum (x :: xs) = x + sum xs

Pred : Set -> Set
Pred A = A -> Set

_∈_ : {A : Set} -> A -> Pred A -> Set
x ∈ P = P x

Not : Set -> Set
Not A = A -> Empty

data Leq : Nat -> Nat -> Set where
  leqZero : {n : Nat} -> Leq zero n
  leqSucc : {m n : Nat} -> Leq m n -> Leq (succ m) (succ n)

leqRefl : (n : Nat) -> Leq n n
leqRefl zero = leqZero
leqRefl (succ n) = leqSucc (leqRefl n)

leqEq : {n m : Nat} -> Eq n m -> Leq n m
leqEq {n} refl = leqRefl n

addZeroRight : (n : Nat) -> Eq (n + zero) n
addZeroRight zero = refl
addZeroRight (succ n) = cong succ (addZeroRight n)

mulOneLeft : (n : Nat) -> Eq (one * n) n
mulOneLeft n = addZeroRight n

mulZeroRight : (n : Nat) -> Eq (n * zero) zero
mulZeroRight zero = refl
mulZeroRight (succ n) = mulZeroRight n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (succ n)
  fsucc : {n : Nat} -> Fin n -> Fin (succ n)

-- Decidability
data Dec (A : Set) : Set where
  yes : A -> Dec A
  no : Not A -> Dec A

-- Boolean operations
not : Bool -> Bool
not true = false
not false = true

_&&_ : Bool -> Bool -> Bool
true && b = b
false && _ = false

_||_ : Bool -> Bool -> Bool
true || _ = true
false || b = b

infixr 6 _&&_
infixr 5 _||_

-- Maybe type
data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : A -> Maybe A

-- Vector type
data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

head : {A : Set} {n : Nat} -> Vec A (succ n) -> A
head (x :: _) = x

tail : {A : Set} {n : Nat} -> Vec A (succ n) -> Vec A n
tail (_ :: xs) = xs

-- Substitution for equality
subst : {A : Set} (P : A -> Set) {x y : A} -> Eq x y -> P x -> P y
subst P refl px = px

-- More equality reasoning
_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} -> Eq x y -> Eq y z -> Eq x z
_ ≡⟨ p ⟩ q = trans p q

_∎ : {A : Set} (x : A) -> Eq x x
_ ∎ = refl

infixr 2 _≡⟨_⟩_
infix 3 _∎

-- More arithmetic lemmas
addSuccRight : (m n : Nat) -> Eq (m + succ n) (succ (m + n))
addSuccRight zero n = refl
addSuccRight (succ m) n = cong succ (addSuccRight m n)

addComm : (m n : Nat) -> Eq (m + n) (n + m)
addComm zero n = sym (addZeroRight n)
addComm (succ m) n = trans (cong succ (addComm m n)) (sym (addSuccRight n m))

addAssoc : (a b c : Nat) -> Eq ((a + b) + c) (a + (b + c))
addAssoc zero b c = refl
addAssoc (succ a) b c = cong succ (addAssoc a b c)

-- Multiplication lemmas
mulSuccRight : (m n : Nat) -> Eq (m * succ n) (m + m * n)
mulSuccRight zero n = refl
mulSuccRight (succ m) n =
  cong succ (trans (cong (n +_) (mulSuccRight m n))
            (trans (sym (addAssoc n m (m * n)))
            (trans (cong (_+ m * n) (addComm n m))
                   (addAssoc m n (m * n)))))

mulComm : (m n : Nat) -> Eq (m * n) (n * m)
mulComm zero n = sym (mulZeroRight n)
mulComm (succ m) n = trans (cong (n +_) (mulComm m n)) (sym (mulSuccRight n m))

-- List utilities
reverse : {A : Set} -> List A -> List A
reverse [] = []
reverse (x :: xs) = reverse xs ++ (x :: [])

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

all : {A : Set} -> (A -> Bool) -> List A -> Bool
all p [] = true
all p (x :: xs) = p x && all p xs

any : {A : Set} -> (A -> Bool) -> List A -> Bool
any p [] = false
any p (x :: xs) = p x || any p xs

-- Propositional all and any for lists
All : {A : Set} -> (A -> Set) -> List A -> Set
All P [] = Unit
All P (x :: xs) = Pair (P x) (All P xs)

Any : {A : Set} -> (A -> Set) -> List A -> Set
Any P [] = Empty
Any P (x :: xs) = Sum (P x) (Any P xs)

-- Inequality utilities
leqTrans : {a b c : Nat} -> Leq a b -> Leq b c -> Leq a c
leqTrans leqZero _ = leqZero
leqTrans (leqSucc p) (leqSucc q) = leqSucc (leqTrans p q)

leqAntiSym : {m n : Nat} -> Leq m n -> Leq n m -> Eq m n
leqAntiSym leqZero leqZero = refl
leqAntiSym (leqSucc p) (leqSucc q) = cong succ (leqAntiSym p q)

leqSuccRight : {m n : Nat} -> Leq m n -> Leq m (succ n)
leqSuccRight leqZero = leqZero
leqSuccRight (leqSucc p) = leqSucc (leqSuccRight p)

-- Natural number comparison
_<=?_ : Nat -> Nat -> Bool
zero <=? n = true
succ m <=? zero = false
succ m <=? succ n = m <=? n

_==?_ : Nat -> Nat -> Bool
zero ==? zero = true
zero ==? succ n = false
succ m ==? zero = false
succ m ==? succ n = m ==? n

-- Max and min
max : Nat -> Nat -> Nat
max zero n = n
max (succ m) zero = succ m
max (succ m) (succ n) = succ (max m n)

min : Nat -> Nat -> Nat
min zero n = zero
min (succ m) zero = zero
min (succ m) (succ n) = succ (min m n)

-- ============================================
-- DIVISION AND MODULAR ARITHMETIC
-- ============================================

-- Division with remainder (returns quotient and remainder)
divMod : Nat -> Nat -> Pair Nat Nat
divMod n zero = pair zero n  -- division by zero: return (0, n)
divMod zero (succ d) = pair zero zero
divMod (succ n) (succ d) with divMod n (succ d)
... | pair q r with succ r ==? succ d
... | true = pair (succ q) zero
... | false = pair q (succ r)

-- Quotient
div : Nat -> Nat -> Nat
div n d = fst (divMod n d)

-- Remainder (modulo)
mod : Nat -> Nat -> Nat
mod n d = snd (divMod n d)

-- Power function
_^_ : Nat -> Nat -> Nat
base ^ zero = one
base ^ succ exp = base * (base ^ exp)

infixr 8 _^_

-- GCD (Euclidean algorithm)
{-# TERMINATING #-}
gcd : Nat -> Nat -> Nat
gcd a zero = a
gcd a (succ b) = gcd (succ b) (mod a (succ b))

-- Coprime: gcd = 1
Coprime : Nat -> Nat -> Set
Coprime a b = Eq (gcd a b) one

-- Divides relation
_∣_ : Nat -> Nat -> Set
d ∣ n = Sigma Nat (\k -> Eq (k * d) n)

-- ============================================
-- DECIDABLE EQUALITY
-- ============================================

decEqNat : (m n : Nat) -> Dec (Eq m n)
decEqNat zero zero = yes refl
decEqNat zero (succ n) = no (\())
decEqNat (succ m) zero = no (\())
decEqNat (succ m) (succ n) with decEqNat m n
... | yes p = yes (cong succ p)
... | no np = no (\{ refl -> np refl })

-- ============================================
-- EXERCISES (holes for students to fill)
-- ============================================

{-
  EXERCISE: Prove that addition is associative
  Fill in the hole to complete the proof.
-}
exercise-addAssoc : (a b c : Nat) -> Eq ((a + b) + c) (a + (b + c))
exercise-addAssoc = addAssoc  -- Students: try proving this yourself!

{-
  EXERCISE: Prove that 0 is a right identity for addition
-}
exercise-addZeroRight : (n : Nat) -> Eq (n + zero) n
exercise-addZeroRight = addZeroRight  -- Students: try proving this yourself!

{-
  EXERCISE: Prove the successor case for addition commutativity
-}
exercise-addSuccRight : (m n : Nat) -> Eq (m + succ n) (succ (m + n))
exercise-addSuccRight = addSuccRight  -- Students: try proving this yourself!
