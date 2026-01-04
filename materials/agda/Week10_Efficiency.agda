{-# OPTIONS --type-in-type #-}

module Week10_Efficiency where

open import Common

-- ============================================
-- ASYMPTOTIC NOTATION
-- ============================================

-- Big-O: f(n) = O(g(n)) iff f(n) ≤ c * g(n) for large n
BigO : (Nat -> Nat) -> (Nat -> Nat) -> Set
BigO f g = Sigma Nat (\c -> Sigma Nat (\n0 -> (n : Nat) -> Leq n0 n -> Leq (f n) (c * g n)))

-- Big-Omega: f(n) = Ω(g(n)) iff f(n) ≥ c * g(n) for large n
BigOmega : (Nat -> Nat) -> (Nat -> Nat) -> Set
BigOmega f g = BigO g f

-- Big-Theta: f(n) = Θ(g(n)) iff f(n) = O(g(n)) and f(n) = Ω(g(n))
BigTheta : (Nat -> Nat) -> (Nat -> Nat) -> Set
BigTheta f g = Pair (BigO f g) (BigOmega f g)

-- Little-o: f(n) = o(g(n)) iff f(n)/g(n) → 0
LittleO : (Nat -> Nat) -> (Nat -> Nat) -> Set
LittleO f g = (c : Nat) -> Leq one c ->
  Sigma Nat (\n0 -> (n : Nat) -> Leq n0 n -> Leq (c * f n) (g n))

-- Little-omega: f(n) = ω(g(n)) iff g(n) = o(f(n))
LittleOmega : (Nat -> Nat) -> (Nat -> Nat) -> Set
LittleOmega f g = LittleO g f

-- ============================================
-- BASIC PROPERTIES
-- ============================================

-- Big-O is reflexive
bigORefl : (f : Nat -> Nat) -> BigO f f
bigORefl f = sigma one (sigma zero proof)
  where
    proof : (n : Nat) -> Leq zero n -> Leq (f n) (one * f n)
    proof n _ = leqEq (sym (mulOneLeft (f n)))

-- Big-O is transitive
postulate
  bigOTrans : {f g h : Nat -> Nat} -> BigO f g -> BigO g h -> BigO f h

-- Constant factors don't matter
postulate
  bigOConst : (f : Nat -> Nat) (c : Nat) -> Leq one c ->
    BigO (\n -> c * f n) f

-- Sum rule: O(f) + O(g) = O(max(f, g))
postulate
  bigOSum : {f g : Nat -> Nat} ->
    BigO (\n -> f n + g n) (\n -> max (f n) (g n))

-- Product rule: O(f) * O(g) = O(f * g)
postulate
  bigOProduct : {f g : Nat -> Nat} ->
    BigO (\n -> f n * g n) (\n -> f n * g n)

-- ============================================
-- COMMON COMPLEXITY CLASSES
-- ============================================

-- Constant: O(1)
constant : Nat -> Nat
constant n = one

-- Logarithmic (approximated as floor(log₂ n))
log2 : Nat -> Nat
log2 zero = zero
log2 (succ zero) = zero
log2 (succ (succ n)) = succ (log2 (succ n))  -- simplified approximation

-- Linear: O(n)
linear : Nat -> Nat
linear n = n

-- Linearithmic: O(n log n)
linearithmic : Nat -> Nat
linearithmic n = n * log2 n

-- Quadratic: O(n²)
quadratic : Nat -> Nat
quadratic n = n * n

-- Cubic: O(n³)
cubic : Nat -> Nat
cubic n = n * n * n

-- Exponential: O(2ⁿ)
exponential : Nat -> Nat
exponential zero = one
exponential (succ n) = succ (succ zero) * exponential n

-- Factorial: O(n!)
factorial : Nat -> Nat
factorial zero = one
factorial (succ n) = succ n * factorial n

-- ============================================
-- COMPLEXITY HIERARCHY
-- ============================================

-- Hierarchy: O(1) ⊂ O(log n) ⊂ O(n) ⊂ O(n log n) ⊂ O(n²) ⊂ O(n³) ⊂ O(2ⁿ) ⊂ O(n!)
postulate
  constSubLog : BigO constant log2
  logSubLinear : BigO log2 linear
  linearSubLinearithmic : BigO linear linearithmic
  linearithmicSubQuadratic : BigO linearithmic quadratic
  quadraticSubCubic : BigO quadratic cubic
  cubicSubExponential : BigO cubic exponential
  exponentialSubFactorial : BigO exponential factorial

-- ============================================
-- RECURRENCE RELATIONS
-- ============================================

-- Master theorem cases (for T(n) = aT(n/b) + f(n))
-- Case 1: f(n) = O(n^(log_b(a) - ε)) => T(n) = Θ(n^(log_b(a)))
-- Case 2: f(n) = Θ(n^(log_b(a))) => T(n) = Θ(n^(log_b(a)) * log(n))
-- Case 3: f(n) = Ω(n^(log_b(a) + ε)) => T(n) = Θ(f(n))

postulate
  masterCase1 : (a b : Nat) (f : Nat -> Nat) ->
    Set  -- Conditions for case 1

  masterCase2 : (a b : Nat) (f : Nat -> Nat) ->
    Set  -- Conditions for case 2

  masterCase3 : (a b : Nat) (f : Nat -> Nat) ->
    Set  -- Conditions for case 3

-- Common recurrences
-- Binary search: T(n) = T(n/2) + O(1) => T(n) = O(log n)
postulate
  binarySearchComplexity : BigO log2 log2

-- Merge sort: T(n) = 2T(n/2) + O(n) => T(n) = O(n log n)
postulate
  mergeSortComplexity : BigO linearithmic linearithmic

-- ============================================
-- ALGORITHM ANALYSIS
-- ============================================

-- Loop complexity: single loop over n elements = O(n)
postulate
  singleLoopComplexity : BigO linear linear

-- Nested loops: two nested loops = O(n²)
postulate
  nestedLoopComplexity : BigO quadratic quadratic

-- Sequential composition: O(f) then O(g) = O(f + g)
postulate
  sequentialComplexity : {f g : Nat -> Nat} ->
    BigO (\n -> f n + g n) (\n -> max (f n) (g n))

-- ============================================
-- AMORTIZED ANALYSIS
-- ============================================

-- Aggregate method: total cost / number of operations
postulate
  aggregateMethod : (totalCost : Nat -> Nat) (numOps : Nat -> Nat) ->
    Nat  -- amortized cost per operation

-- Accounting method: assign amortized costs that cover actual costs
postulate
  accountingMethod : Set

-- Potential method: define potential function
postulate
  potentialMethod : (Nat -> Nat) -> Set

-- ============================================
-- SPACE COMPLEXITY
-- ============================================

-- Space complexity
SpaceO : (Nat -> Nat) -> (Nat -> Nat) -> Set
SpaceO = BigO

-- In-place algorithm: O(1) extra space
InPlace : (Nat -> Nat) -> Set
InPlace f = SpaceO f constant

-- Linear space
LinearSpace : (Nat -> Nat) -> Set
LinearSpace f = SpaceO f linear

-- Time-space tradeoff
postulate
  timeSpaceTradeoff : Set  -- General principle

-- ============================================
-- COMPLEXITY CLASSES (Decision Problems)
-- ============================================

-- P: solvable in polynomial time
postulate
  P : Set -> Set

-- NP: verifiable in polynomial time
postulate
  NP : Set -> Set

-- P ⊆ NP
postulate
  pSubsetNP : {A : Set} -> P A -> NP A

-- NP-complete: hardest problems in NP
postulate
  NPComplete : Set -> Set

-- NP-hard: at least as hard as NP-complete
postulate
  NPHard : Set -> Set

-- P vs NP problem (open)
postulate
  pVsNP : Sum ((A : Set) -> P A -> NP A -> P A) Unit  -- either P = NP or unknown
