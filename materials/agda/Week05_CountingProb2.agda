{-# OPTIONS --type-in-type #-}

module Week05_CountingProb2 where

open import Common

-- Factorial
fact : Nat -> Nat
fact zero = one
fact (succ n) = succ n * fact n

-- Binomial coefficients (n choose k)
choose : Nat -> Nat -> Nat
choose n zero = one
choose zero (succ k) = zero
choose (succ n) (succ k) = choose n (succ k) + choose n k

-- Basic properties of binomial coefficients

-- C(n, 0) = 1
chooseZero : (n : Nat) -> Eq (choose n zero) one
chooseZero n = refl

-- C(n, n) = 1
-- Proof: C(n, n) = C(n-1, n) + C(n-1, n-1) = 0 + C(n-1, n-1) = ... = C(0, 0) = 1
postulate
  chooseN : (n : Nat) -> Eq (choose n n) one

-- Pascal's identity: C(n+1, k+1) = C(n, k+1) + C(n, k)
pascal : (n k : Nat) -> Eq (choose (succ n) (succ k)) (choose n (succ k) + choose n k)
pascal n k = refl

-- Symmetry: C(n, k) = C(n, n-k)
postulate
  chooseSym : (n k : Nat) -> Leq k n -> Eq (choose n k) (choose n (n - k))

-- Sum of row: sum of C(n, k) for k = 0 to n equals 2^n
sumRow : Nat -> Nat
sumRow zero = one
sumRow (succ n) = sumRow n + sumRow n  -- By Pascal's identity and induction

-- Stars and bars: number of ways to put n identical items into k bins
-- Equivalently: number of non-negative integer solutions to x1 + ... + xk = n
starsAndBars : Nat -> Nat -> Nat
starsAndBars n k = choose ((n + k) - one) (k - one)

-- Multichoose: C(n+k-1, k) = "n multichoose k"
-- Number of ways to choose k items from n types with repetition
multichoose : Nat -> Nat -> Nat
multichoose n k = choose ((n + k) - one) k

-- Compositions: number of ways to write n as an ordered sum of k positive integers
compositions : Nat -> Nat -> Nat
compositions n k = choose (n - one) (k - one)

-- Helper: generate a list [0, 1, ..., n-1]
range : Nat -> List Nat
range zero = []
range (succ n) = n :: range n

-- Vandermonde's identity: C(m+n, r) = sum_{k=0}^r C(m, k) * C(n, r-k)
postulate
  vandermonde : (m n r : Nat) ->
    Eq (choose (m + n) r)
       (sum (map (\k -> choose m k * choose n (r - k)) (range (succ r))))

-- Hockey stick identity: sum of C(i, k) for i = k to n equals C(n+1, k+1)
postulate
  hockeyStick : (n k : Nat) -> Leq k n ->
    Eq (sum (map (\i -> choose i k) (range (succ n))))
       (choose (succ n) (succ k))

-- Binomial theorem coefficients
-- The coefficient of x^k y^(n-k) in (x+y)^n is C(n, k)

-- Multinomial coefficient
-- Number of ways to partition n items into groups of sizes k1, k2, ..., km
-- where k1 + k2 + ... + km = n
multinomial : List Nat -> Nat
multinomial [] = one
multinomial (k :: ks) = choose (sum (k :: ks)) k * multinomial ks

-- Catalan numbers: C_n = C(2n, n) / (n+1)
-- Counts: valid parentheses, binary trees, non-crossing partitions, etc.
postulate
  catalan : Nat -> Nat
  catalanRecurrence : (n : Nat) ->
    Eq (catalan (succ n))
       (sum (map (\k -> catalan k * catalan (n - k)) (range (succ n))))

-- Stirling numbers of the second kind S(n, k)
-- Number of ways to partition n elements into k non-empty subsets
stirling2 : Nat -> Nat -> Nat
stirling2 zero zero = one
stirling2 zero (succ k) = zero
stirling2 (succ n) zero = zero
stirling2 (succ n) (succ k) = succ k * stirling2 n (succ k) + stirling2 n k

-- Bell numbers: total number of partitions of n elements
bell : Nat -> Nat
bell n = sum (map (stirling2 n) (range (succ n)))

-- Probability axioms (using natural number ratios as approximation)
-- P(E) represented as a pair (numerator, denominator)
Probability : Set
Probability = Pair Nat Nat

-- Probability must be between 0 and 1
ValidProb : Probability -> Set
ValidProb (pair num den) = Pair (Leq num den) (Leq one den)

-- Complement probability: P(E^c) = 1 - P(E)
probComplement : Probability -> Probability
probComplement (pair num den) = pair (den - num) den

-- Addition for disjoint events: P(A ∪ B) = P(A) + P(B)
probAddDisjoint : Probability -> Probability -> Probability
probAddDisjoint (pair n1 d1) (pair n2 d2) = pair (n1 * d2 + n2 * d1) (d1 * d2)

-- Conditional probability: P(A | B) = P(A ∩ B) / P(B)
-- Represented as function from P(A ∩ B) and P(B) to P(A | B)
condProb : Probability -> Probability -> Probability
condProb (pair nAB dAB) (pair nB dB) = pair (nAB * dB) (dAB * nB)

-- Independence: P(A ∩ B) = P(A) * P(B)
Independent : Probability -> Probability -> Probability -> Set
Independent pA pB pAB with pA | pB | pAB
... | pair nA dA | pair nB dB | pair nAB dAB = Eq (nAB * dA * dB) (nA * nB * dAB)

-- ============================================
-- DERANGEMENTS
-- ============================================

{-
  A derangement is a permutation with no fixed points.
  D(n) = number of derangements of n elements

  Formula: D(n) = n! * Σ_{k=0}^{n} (-1)^k / k!
  Recurrence: D(n) = (n-1) * (D(n-1) + D(n-2))

  For large n: D(n) ≈ n!/e
-}

-- Derangement count
derangement : Nat -> Nat
derangement zero = one           -- D(0) = 1 (empty permutation)
derangement (succ zero) = zero   -- D(1) = 0 (no derangements)
derangement (succ (succ n)) =
  succ n * (derangement (succ n) + derangement n)

-- Small values
-- D(0) = 1, D(1) = 0, D(2) = 1, D(3) = 2, D(4) = 9, D(5) = 44

-- Hat-check probability: D(n)/n! ≈ 1/e ≈ 0.368
-- The probability that no one gets their own hat

-- ============================================
-- INCLUSION-EXCLUSION PRINCIPLE
-- ============================================

{-
  |A₁ ∪ A₂ ∪ ... ∪ Aₙ| =
    Σ|Aᵢ| - Σ|Aᵢ ∩ Aⱼ| + Σ|Aᵢ ∩ Aⱼ ∩ Aₖ| - ...

  This is the generalization of:
  |A ∪ B| = |A| + |B| - |A ∩ B|
-}

-- For two sets
inclusionExclusion2 : Nat -> Nat -> Nat -> Nat
inclusionExclusion2 countA countB countAB = (countA + countB) - countAB

-- For three sets
inclusionExclusion3 : Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat
inclusionExclusion3 a b c ab ac bc abc =
  (a + b + c) - (ab + ac + bc) + abc

-- Number of surjective functions from n-element set to k-element set
-- Using inclusion-exclusion: k! * S(n, k) where S is Stirling number
surjections : Nat -> Nat -> Nat
surjections n k = fact k * stirling2 n k

-- ============================================
-- EXERCISES
-- ============================================

{-
  EXERCISE 1: Prove C(n, 0) = 1 for all n
-}
exercise-chooseZero : (n : Nat) -> Eq (choose n zero) one
exercise-chooseZero n = refl

{-
  EXERCISE 2: Compute C(5, 2) and verify it equals 10
-}
exercise-choose52 : Eq (choose (succ (succ (succ (succ (succ zero)))))
                              (succ (succ zero)))
                      (succ (succ (succ (succ (succ
                       (succ (succ (succ (succ (succ zero))))))))))
exercise-choose52 = refl

{-
  EXERCISE 3: Verify D(4) = 9
-}
exercise-derangement4 : Eq (derangement (succ (succ (succ (succ zero)))))
                          (succ (succ (succ (succ (succ
                           (succ (succ (succ (succ zero)))))))))
exercise-derangement4 = refl

{-
  EXERCISE 4: Prove the recurrence for Stirling numbers
  S(n+1, k+1) = (k+1) * S(n, k+1) + S(n, k)
-}
exercise-stirlingRecurrence : (n k : Nat) ->
  Eq (stirling2 (succ n) (succ k))
     (succ k * stirling2 n (succ k) + stirling2 n k)
exercise-stirlingRecurrence n k = refl

{-
  EXERCISE 5: Show that S(n, 1) = 1 (one way to put n items in 1 subset)
  Hint: Use induction and the recurrence
-}
postulate
  exercise-stirlingOne : (n : Nat) -> Leq one n -> Eq (stirling2 n one) one

{-
  EXERCISE 6: Show that S(n, n) = 1 (one way: each element in own subset)
-}
postulate
  exercise-stirlingN : (n : Nat) -> Eq (stirling2 n n) one
