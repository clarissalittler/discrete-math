{-# OPTIONS --type-in-type #-}

module Week04_CountingProb1 where

open import Common

-- Sample space and events
SampleSpace : Set -> Set
SampleSpace A = A

Event : Set -> Set
Event A = Pred A

-- Events are subsets of the sample space
_∈E_ : {A : Set} -> A -> Event A -> Set
x ∈E E = E x

-- Complement of an event
EventCompl : {A : Set} -> Event A -> Event A
EventCompl E x = Not (E x)

-- Intersection of events (both occur)
_∩E_ : {A : Set} -> Event A -> Event A -> Event A
(E1 ∩E E2) x = Pair (E1 x) (E2 x)

-- Union of events (at least one occurs)
_∪E_ : {A : Set} -> Event A -> Event A -> Event A
(E1 ∪E E2) x = Sum (E1 x) (E2 x)

-- Disjoint (mutually exclusive) events
Disjoint : {A : Set} -> Event A -> Event A -> Set
Disjoint {A} P Q = (x : A) -> P x -> Q x -> Empty

-- Partition of events (pairwise disjoint and exhaustive)
Exhaustive : {A : Set} -> List (Event A) -> Set
Exhaustive {A} events = (x : A) -> Any (\E -> E x) events

-- Counting principles
-- Multiplication rule: |A × B| = |A| * |B|
countProduct : Nat -> Nat -> Nat
countProduct m n = m * n

-- Addition rule for disjoint sets: |A ∪ B| = |A| + |B| (when disjoint)
countSum : Nat -> Nat -> Nat
countSum m n = m + n

-- Inclusion-exclusion for two sets: |A ∪ B| = |A| + |B| - |A ∩ B|
countUnion : Nat -> Nat -> Nat -> Nat
countUnion countA countB inter = (countA + countB) - inter

-- Subtraction rule: |A - B| = |A| - |A ∩ B|
countDifference : Nat -> Nat -> Nat
countDifference countA countInter = countA - countInter

-- Complement rule: |A^c| = |S| - |A|
countComplement : Nat -> Nat -> Nat
countComplement sampleSize countA = sampleSize - countA

-- Finite sets with decidable equality
record Finite (A : Set) : Set where
  field
    size : Nat
    enumerate : Vec A size

-- Pigeonhole principle
-- If n+1 pigeons are placed in n holes, at least one hole contains at least 2 pigeons
data Collision {A : Set} : List A -> Set where
  collisionHere : {x : A} {xs : List A} -> x ∈ (\y -> Any (\z -> Eq z y) xs) -> Collision (x :: xs)
  collisionThere : {x : A} {xs : List A} -> Collision xs -> Collision (x :: xs)

-- Abstract pigeonhole: more inputs than outputs implies collision
postulate
  pigeonhole : {A B : Set} ->
    (f : A -> B) ->
    (pigeons : Nat) ->
    (holes : Nat) ->
    Leq (succ holes) pigeons ->
    -- Given a finite enumeration of inputs and outputs,
    -- there exist distinct inputs mapping to the same output
    Set

-- Generalized pigeonhole principle
-- If n items are placed in k boxes, at least one box has ⌈n/k⌉ items
postulate
  generalizedPigeonhole : (items boxes : Nat) ->
    (f : Fin items -> Fin boxes) ->
    Leq boxes items ->
    Sigma (Fin boxes) (\box -> Set)

-- Permutations
-- Number of ways to arrange n distinct items: n!
Factorial : Nat -> Nat
Factorial zero = one
Factorial (succ n) = succ n * Factorial n

-- Partial permutations (k-permutations of n items)
-- P(n,k) = n!/(n-k)!
Permutation : Nat -> Nat -> Nat
Permutation n zero = one
Permutation zero (succ k) = zero
Permutation (succ n) (succ k) = succ n * Permutation n k

-- Factorial properties
postulate
  factorialPositive : (n : Nat) -> Leq one (Factorial n)

-- Product of consecutive integers
-- n * (n-1) * ... * (n-k+1)
fallingFactorial : Nat -> Nat -> Nat
fallingFactorial n zero = one
fallingFactorial zero (succ k) = zero
fallingFactorial (succ n) (succ k) = succ n * fallingFactorial n k

-- Rising factorial (Pochhammer symbol)
risingFactorial : Nat -> Nat -> Nat
risingFactorial n zero = one
risingFactorial n (succ k) = (n + k) * risingFactorial n k

-- Derangements: permutations with no fixed points
-- D(n) ≈ n!/e (no element appears in its original position)
postulate
  Derangement : Nat -> Nat
  derangementRecurrence : (n : Nat) ->
    Eq (Derangement (succ (succ n)))
       ((succ n) * (Derangement (succ n) + Derangement n))

-- Counting functions
-- Number of functions from A to B: |B|^|A|
countFunctions : Nat -> Nat -> Nat
countFunctions domain zero = zero
countFunctions zero codomain = one
countFunctions (succ d) codomain = codomain * countFunctions d codomain

-- Number of injections from A to B (when |A| ≤ |B|): P(|B|, |A|)
countInjections : Nat -> Nat -> Nat
countInjections = Permutation

-- Subset counting
-- Number of subsets of an n-element set: 2^n
countSubsets : Nat -> Nat
countSubsets n = countFunctions n (succ (succ zero))
