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
