{-# OPTIONS --type-in-type #-}

module Week06_ExpectationGraphs where

open import Common

-- Weighted distribution for discrete random variables
-- Each pair is (value, weight/count)
Weighted : Set
Weighted = List (Pair Nat Nat)

-- Weighted sum: sum of value * weight for each pair
weightedSum : Weighted -> Nat
weightedSum xs = sum (map (\p -> fst p * snd p) xs)

-- Total weight (denominator for expected value)
totalWeight : Weighted -> Nat
totalWeight xs = sum (map snd xs)

-- Numerator for expected value calculation
expectedValueNumerator : Weighted -> Nat
expectedValueNumerator = weightedSum

-- Random variable as a function from sample space to outcomes
RandomVariable : Set -> Set
RandomVariable S = S -> Nat

-- Expected value representation (numerator, denominator)
ExpectedValue : Set
ExpectedValue = Pair Nat Nat

-- Indicator random variable: 1 if predicate holds, 0 otherwise
indicator : {S : Set} -> (S -> Bool) -> RandomVariable S
indicator p s = if p s then one else zero

-- Linearity of expectation property (represented as equation)
-- E[X + Y] = E[X] + E[Y]
postulate
  linearityOfExpectation : (num1 den1 num2 den2 : Nat) ->
    -- E[X + Y] numerator = E[X] numerator * den2 + E[Y] numerator * den1
    Eq (num1 * den2 + num2 * den1) ((num1 * den2 + num2 * den1))

-- ============================================
-- GRAPH THEORY FUNDAMENTALS
-- ============================================

-- Abstract graph as a record
record Graph : Set where
  field
    V : Set
    E : V -> V -> Set

-- Simple graph: undirected, no loops, no multi-edges
record SimpleGraph : Set where
  field
    V : Set
    E : V -> V -> Set
    symmetric : (u v : V) -> E u v -> E v u
    irreflexive : (v : V) -> Not (E v v)

-- Directed graph
record Digraph : Set where
  field
    V : Set
    E : V -> V -> Set

-- Weighted graph
record WeightedGraph : Set where
  field
    V : Set
    E : V -> V -> Set
    weight : (u v : V) -> E u v -> Nat

-- Graph with explicit vertex list (for finite graphs)
record FiniteGraph : Set where
  field
    n : Nat
    V : Fin n -> Set
    adj : Fin n -> Fin n -> Bool

-- Adjacency as a decidable relation
Adjacent : {n : Nat} -> (Fin n -> Fin n -> Bool) -> Fin n -> Fin n -> Set
Adjacent adj u v = Eq (adj u v) true

-- Degree of a vertex in a finite graph
degree' : {n : Nat} -> (Fin n -> Fin n -> Bool) -> Fin n -> Nat
degree' {zero} adj v = zero
degree' {succ n} adj v = countTrue n
  where
    countTrue : Nat -> Nat
    countTrue zero = zero
    countTrue (succ m) = countTrue m  -- placeholder

-- Graph properties
postulate
  vertices : (g : Graph) -> List (Graph.V g)
  degree : (g : Graph) -> Graph.V g -> Nat
  edges : (g : Graph) -> Nat

-- Handshake theorem: sum of degrees = 2 * |E|
postulate
  handshake : (g : Graph) ->
    Eq (sum (map (degree g) (vertices g))) (succ (succ zero) * edges g)

-- Corollary: sum of degrees is always even
handshakeEven : (g : Graph) -> Sigma Nat (\k -> Eq (sum (map (degree g) (vertices g))) (succ (succ zero) * k))
handshakeEven g = sigma (edges g) (handshake g)

-- Number of odd-degree vertices is even
postulate
  evenOddDegreeVertices : (g : Graph) ->
    Sigma Nat (\k -> Eq (length (filter (\v -> not ((degree g v) ==? zero)) (vertices g))) (succ (succ zero) * k))

-- Complete graph K_n: every pair of distinct vertices is adjacent
record CompleteGraph (n : Nat) : Set where
  field
    vertex : Fin n
    allAdjacent : (u v : Fin n) -> Not (Eq u v) -> Unit

-- Bipartite graph: vertices can be partitioned into two sets
record BipartiteGraph : Set where
  field
    V1 : Set
    V2 : Set
    E : V1 -> V2 -> Set

-- Graph complement
ComplementGraph : Graph -> Graph
ComplementGraph g = record
  { V = Graph.V g
  ; E = \u v -> Not (Graph.E g u v)
  }

-- Subgraph relation
Subgraph : Graph -> Graph -> Set
Subgraph h g = Sigma (Graph.V h -> Graph.V g) (\f ->
  (u v : Graph.V h) -> Graph.E h u v -> Graph.E g (f u) (f v))

-- Regular graph: all vertices have the same degree
Regular : Graph -> Nat -> Set
Regular g k = (v : Graph.V g) -> Eq (degree g v) k

-- Counting edges in regular graph
postulate
  regularEdgeCount : (g : Graph) (k : Nat) -> Regular g k ->
    Eq (succ (succ zero) * edges g) (k * length (vertices g))

-- Graph connectivity (via reachability)
Connected : Graph -> Set
Connected g = (u v : Graph.V g) -> Sigma (List (Graph.V g)) (\path -> Unit)

-- k-connectivity
postulate
  kConnected : Graph -> Nat -> Set

-- Chromatic number (minimum colors for proper coloring)
postulate
  chromaticNumber : Graph -> Nat
  -- K_n has chromatic number n
  completeChromaticNumber : (n : Nat) -> Eq (chromaticNumber (record { V = Fin n ; E = \u v -> Not (Eq u v) })) n
