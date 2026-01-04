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
