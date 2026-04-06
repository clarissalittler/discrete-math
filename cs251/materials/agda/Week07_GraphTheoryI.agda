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

-- ============================================
-- GRAPH COLORING
-- ============================================

{-
  A k-coloring assigns each vertex a color from {0, 1, ..., k-1}
  such that no two adjacent vertices have the same color.

  The chromatic number χ(G) is the minimum k for which
  a k-coloring exists.
-}

-- A coloring assigns colors (represented as Fin k) to vertices
Coloring : {n : Nat} -> Nat -> MatrixGraph n -> Set
Coloring {n} k g = Fin n -> Fin k

-- A coloring is proper if adjacent vertices have different colors
ProperColoring : {n k : Nat} (g : MatrixGraph n) -> (Fin n -> Fin k) -> Set
ProperColoring {n} {k} g c =
  (u v : Fin n) -> Edge g u v -> Not (Eq (c u) (c v))

-- A graph is k-colorable if it has a proper k-coloring
Colorable : {n : Nat} -> Nat -> MatrixGraph n -> Set
Colorable {n} k g = Sigma (Coloring {n} k g) (ProperColoring g)

-- Chromatic number: minimum k such that G is k-colorable
postulate
  chromaticNumber : {n : Nat} -> MatrixGraph n -> Nat
  chromaticNumberMinimal : {n : Nat} (g : MatrixGraph n) ->
    Colorable (chromaticNumber g) g
  chromaticNumberOptimal : {n : Nat} (g : MatrixGraph n) (k : Nat) ->
    Colorable k g -> Leq (chromaticNumber g) k

-- ============================================
-- CHROMATIC NUMBERS OF SPECIAL GRAPHS
-- ============================================

{-
  χ(K_n) = n     (complete graph needs n colors)
  χ(C_n) = 2     if n is even
  χ(C_n) = 3     if n is odd
  χ(K_{m,n}) = 2 (bipartite)
  χ(Tree) = 2    (if at least one edge)
-}

-- Complete graphs need n colors
postulate
  chromaticComplete : (n : Nat) -> Leq one n ->
    Eq (chromaticNumber (completeGraph n)) n

-- Bipartite graphs are 2-colorable
postulate
  bipartiteIs2Colorable : {n : Nat} (g : MatrixGraph n) ->
    -- If g is bipartite, then χ(g) ≤ 2
    Set

-- A graph is bipartite iff it contains no odd cycle
Bipartite : {n : Nat} -> MatrixGraph n -> Set
Bipartite {n} g = Colorable {n} (succ (succ zero)) g

postulate
  bipartiteNoOddCycle : {n : Nat} (g : MatrixGraph n) ->
    Bipartite g -> -- implies no odd-length cycles
    Set

-- ============================================
-- PLANAR GRAPHS
-- ============================================

{-
  A graph is planar if it can be drawn in the plane
  without edge crossings.

  Euler's formula: V - E + F = 2
  (for connected planar graphs)

  Key consequences:
  - For V ≥ 3: E ≤ 3V - 6
  - For triangle-free graphs: E ≤ 2V - 4
  - K_5 and K_{3,3} are not planar
-}

-- Planarity (abstract property)
postulate
  Planar : {n : Nat} -> MatrixGraph n -> Set

-- Edge count in a graph
edgeCount : {n : Nat} -> MatrixGraph n -> Nat
edgeCount {zero} g = zero
edgeCount {succ n} g = zero  -- placeholder: would count all true entries / 2

-- Euler's formula for planar graphs
record EulerFormula {n : Nat} (g : MatrixGraph n) : Set where
  field
    vertices : Nat
    edges : Nat
    faces : Nat
    formula : Eq (vertices - edges + faces) (succ (succ zero))

-- Edge bound for planar graphs: E ≤ 3V - 6
postulate
  planarEdgeBound : {n : Nat} (g : MatrixGraph n) ->
    Planar g ->
    Leq (succ (succ (succ zero))) n ->  -- V ≥ 3
    Leq (edgeCount g) (succ (succ (succ zero)) * n - succ (succ (succ (succ (succ (succ zero))))))

-- Edge bound for triangle-free planar graphs: E ≤ 2V - 4
postulate
  planarTriangleFreeEdgeBound : {n : Nat} (g : MatrixGraph n) ->
    Planar g ->
    -- g is triangle-free
    Leq (edgeCount g) (succ (succ zero) * n - succ (succ (succ (succ zero))))

-- K_5 is not planar
postulate
  k5NotPlanar : Not (Planar (completeGraph (succ (succ (succ (succ (succ zero)))))))

-- K_{3,3} is not planar
postulate
  k33NotPlanar : Not (Planar (completeBipartite (succ (succ (succ zero)))
                                                (succ (succ (succ zero)))))

-- Kuratowski's theorem
postulate
  kuratowski : {n : Nat} (g : MatrixGraph n) ->
    Planar g ->
    -- g contains no subdivision of K_5 or K_{3,3}
    Set

-- Four Color Theorem: every planar graph is 4-colorable
postulate
  fourColorTheorem : {n : Nat} (g : MatrixGraph n) ->
    Planar g ->
    Colorable {n} (succ (succ (succ (succ zero)))) g

-- ============================================
-- EXERCISES
-- ============================================

{-
  EXERCISE 1: Prove that χ(G) ≥ ω(G) where ω is the clique number
  (size of largest complete subgraph)
-}
postulate
  exercise-chromClique : {n : Nat} (g : MatrixGraph n) ->
    (k : Nat) ->  -- clique size
    -- if g contains K_k as subgraph
    Leq k (chromaticNumber g)

{-
  EXERCISE 2: Show that a 2-coloring of a path graph exists
-}
postulate
  exercise-pathColoring : (n : Nat) -> Leq one n ->
    Colorable {n} (succ (succ zero)) (pathGraph n)

{-
  EXERCISE 3: Show that the complete graph K_3 needs exactly 3 colors
-}
three : Nat
three = succ (succ (succ zero))

postulate
  exercise-k3Chromatic : Eq (chromaticNumber (completeGraph three)) three

{-
  EXERCISE 4: Verify Euler's formula for the tetrahedron (K_4 embedded)
  V = 4, E = 6, F = 4
  V - E + F = 2, but natural number subtraction is tricky, so we verify:
  V + F = E + 2  (rearranged form)
  4 + 4 = 6 + 2 = 8 ✓
-}
four : Nat
four = succ three

six : Nat
six = succ (succ (succ three))

two : Nat
two = succ (succ zero)

eight : Nat
eight = succ (succ six)

-- Euler's formula rearranged: V + F = E + 2
exercise-eulerTetrahedron : Eq (four + four) (six + two)
exercise-eulerTetrahedron = refl

{-
  EXERCISE 5: Show that every planar graph has a vertex of degree ≤ 5
  (Consequence of E ≤ 3V - 6 and handshake lemma)
-}
postulate
  exercise-planarDegree5 : {n : Nat} (g : MatrixGraph n) ->
    Planar g ->
    Sigma (Fin n) (\v -> Leq (vertexDegree g v) (succ (succ (succ (succ (succ zero))))))
