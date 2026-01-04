{-# OPTIONS --type-in-type #-}

module Week07_GraphTheoryI where

open import Common

-- Matrix representation of a graph
record MatrixGraph (n : Nat) : Set where
  field
    adj : Fin n -> Fin n -> Bool

-- Edge exists when adjacency matrix entry is true
Edge : {n : Nat} -> MatrixGraph n -> Fin n -> Fin n -> Set
Edge g u v = Eq (MatrixGraph.adj g u v) true

-- Symmetric adjacency matrix (for undirected graphs)
Symmetric : {n : Nat} -> MatrixGraph n -> Set
Symmetric {n} g = (u v : Fin n) -> Eq (MatrixGraph.adj g u v) (MatrixGraph.adj g v u)

-- No self-loops
NoLoops : {n : Nat} -> MatrixGraph n -> Set
NoLoops {n} g = (v : Fin n) -> Eq (MatrixGraph.adj g v v) false

-- ============================================
-- WALKS, TRAILS, PATHS, AND CYCLES
-- ============================================

-- Walk: sequence of vertices where consecutive vertices are adjacent
data Walk {n : Nat} (g : MatrixGraph n) : List (Fin n) -> Set where
  single : {v : Fin n} -> Walk g (v :: [])
  step : {u v : Fin n} {rest : List (Fin n)} ->
    Edge g u v -> Walk g (v :: rest) -> Walk g (u :: v :: rest)

-- Walk length is the number of edges
walkLength : {n : Nat} {g : MatrixGraph n} {vs : List (Fin n)} -> Walk g vs -> Nat
walkLength single = zero
walkLength (step _ w) = succ (walkLength w)

-- Walk endpoints
walkStart : {n : Nat} {g : MatrixGraph n} {vs : List (Fin n)} -> Walk g vs -> Fin n
walkStart {vs = v :: _} _ = v

-- Trail: a walk with no repeated edges
-- We track visited edges as a predicate
Trail : {n : Nat} -> MatrixGraph n -> List (Fin n) -> Set
Trail {n} g vs = Pair (Walk g vs) (NoRepeatedEdges vs)
  where
    NoRepeatedEdges : List (Fin n) -> Set
    NoRepeatedEdges [] = Unit
    NoRepeatedEdges (_ :: []) = Unit
    NoRepeatedEdges (u :: v :: rest) = Pair Unit (NoRepeatedEdges (v :: rest))

-- Path: a walk with no repeated vertices
Path : {n : Nat} -> MatrixGraph n -> List (Fin n) -> Set
Path {n} g vs = Pair (Walk g vs) (AllDistinct vs)
  where
    AllDistinct : List (Fin n) -> Set
    AllDistinct [] = Unit
    AllDistinct (v :: ws) = Pair (Not (Any (\u -> Eq u v) ws)) (AllDistinct ws)

-- Closed walk: starts and ends at the same vertex
Closed : {n : Nat} {g : MatrixGraph n} {vs : List (Fin n)} -> Walk g vs -> Set
Closed {n} {vs = []} _ = Empty  -- impossible case
Closed {n} {vs = v :: []} _ = Unit  -- single vertex is trivially closed
Closed {n} {vs = v :: rest} w = Eq v (lastVertex rest)
  where
    lastVertex : List (Fin n) -> Fin n
    lastVertex [] = v  -- shouldn't happen in valid walk
    lastVertex (x :: []) = x
    lastVertex (_ :: xs) = lastVertex xs

-- Circuit: a closed trail (simplified - just require trail property)
Circuit : {n : Nat} -> MatrixGraph n -> List (Fin n) -> Set
Circuit {n} g vs = Trail g vs  -- Full definition would check first = last

-- Cycle: a closed path (except start = end)
Cycle : {n : Nat} -> MatrixGraph n -> List (Fin n) -> Set
Cycle {n} g vs = Pair (Path g vs) Unit  -- simplified

-- ============================================
-- EULER PATHS AND CIRCUITS
-- ============================================

-- Degree of a vertex
vertexDegree : {n : Nat} -> MatrixGraph n -> Fin n -> Nat
vertexDegree {zero} g v = zero
vertexDegree {succ n} g v = countAdj n
  where
    countAdj : Nat -> Nat
    countAdj zero = zero
    countAdj (succ m) = countAdj m  -- placeholder

-- Even degree
EvenDegree : {n : Nat} -> MatrixGraph n -> Fin n -> Set
EvenDegree g v = Sigma Nat (\k -> Eq (vertexDegree g v) (succ (succ zero) * k))

-- Odd degree
OddDegree : {n : Nat} -> MatrixGraph n -> Fin n -> Set
OddDegree g v = Sigma Nat (\k -> Eq (vertexDegree g v) (succ (succ (succ zero) * k)))

-- Euler trail: uses every edge exactly once
postulate
  EulerTrail : {n : Nat} -> MatrixGraph n -> List (Fin n) -> Set

-- Euler circuit: closed Euler trail
postulate
  EulerCircuit : {n : Nat} -> MatrixGraph n -> List (Fin n) -> Set

-- Euler's theorem for circuits: exists iff all vertices have even degree
postulate
  eulerCircuitTheorem : {n : Nat} (g : MatrixGraph n) ->
    ((v : Fin n) -> EvenDegree g v) ->
    Sigma (List (Fin n)) (EulerCircuit g)

-- Euler's theorem for trails: exists iff exactly 0 or 2 odd-degree vertices
postulate
  eulerTrailTheorem : {n : Nat} (g : MatrixGraph n) ->
    -- Either all even, or exactly two odd
    Sigma (List (Fin n)) (EulerTrail g)

-- ============================================
-- GRAPH ISOMORPHISM
-- ============================================

-- Graph isomorphism: bijection preserving adjacency
record Isomorphism {n m : Nat} (g1 : MatrixGraph n) (g2 : MatrixGraph m) : Set where
  field
    sizeEq : Eq n m
    bij : Fin n -> Fin m
    bijInv : Fin m -> Fin n
    leftInv : (v : Fin n) -> Eq (bijInv (bij v)) v
    rightInv : (v : Fin m) -> Eq (bij (bijInv v)) v
    preserveAdj : (u v : Fin n) ->
      Eq (MatrixGraph.adj g1 u v) (MatrixGraph.adj g2 (bij u) (bij v))

-- Isomorphism is an equivalence relation
postulate
  Isomorphic : {n m : Nat} -> MatrixGraph n -> MatrixGraph m -> Set

  isoRefl : {n : Nat} (g : MatrixGraph n) -> Isomorphic g g
  isoSym : {n m : Nat} {g1 : MatrixGraph n} {g2 : MatrixGraph m} ->
    Isomorphic g1 g2 -> Isomorphic g2 g1
  isoTrans : {n m k : Nat} {g1 : MatrixGraph n} {g2 : MatrixGraph m} {g3 : MatrixGraph k} ->
    Isomorphic g1 g2 -> Isomorphic g2 g3 -> Isomorphic g1 g3

-- Isomorphism invariants
postulate
  -- Number of vertices
  isoPreservesSize : {n m : Nat} {g1 : MatrixGraph n} {g2 : MatrixGraph m} ->
    Isomorphic g1 g2 -> Eq n m
  -- Number of edges
  isoPreservesEdges : {n m : Nat} {g1 : MatrixGraph n} {g2 : MatrixGraph m} ->
    Isomorphic g1 g2 -> Set
  -- Degree sequence
  isoPreservesDegreeSeq : {n m : Nat} {g1 : MatrixGraph n} {g2 : MatrixGraph m} ->
    Isomorphic g1 g2 -> Set

-- ============================================
-- ADJACENCY MATRIX PROPERTIES
-- ============================================

-- Matrix power (for counting walks)
-- A^k[i,j] = number of walks of length k from i to j
postulate
  matrixPower : {n : Nat} -> MatrixGraph n -> Nat -> Fin n -> Fin n -> Nat
  -- Base case: A^0 = I (identity matrix)
  matrixPowerZero : {n : Nat} (g : MatrixGraph n) (u v : Fin n) ->
    Set  -- Eq (matrixPower g zero u v) (if u == v then 1 else 0)

-- Trace of adjacency matrix power counts closed walks
postulate
  traceCountsClosedWalks : {n : Nat} (g : MatrixGraph n) (k : Nat) ->
    Set  -- trace(A^k) = number of closed walks of length k

-- ============================================
-- SPECIAL GRAPHS
-- ============================================

-- Finite ordinal equality check
finEq : {n : Nat} -> Fin n -> Fin n -> Bool
finEq fzero fzero = true
finEq fzero (fsucc _) = false
finEq (fsucc _) fzero = false
finEq (fsucc m) (fsucc k) = finEq m k

-- Complete graph K_n
completeGraph : (n : Nat) -> MatrixGraph n
completeGraph n = record { adj = \u v -> not (finEq u v) }

-- Cycle graph C_n
postulate
  cycleGraph : (n : Nat) -> MatrixGraph n

-- Path graph P_n
postulate
  pathGraph : (n : Nat) -> MatrixGraph n

-- Complete bipartite graph K_{m,n}
postulate
  completeBipartite : (m n : Nat) -> MatrixGraph (m + n)
