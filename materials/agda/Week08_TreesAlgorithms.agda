{-# OPTIONS --type-in-type #-}

module Week08_TreesAlgorithms where

open import Common

-- ============================================
-- TREE DATA STRUCTURES
-- ============================================

-- General tree with variable branching (rose tree)
data Tree (A : Set) : Set where
  node : A -> List (Tree A) -> Tree A

-- Binary tree
data BinTree (A : Set) : Set where
  leaf : BinTree A
  branch : A -> BinTree A -> BinTree A -> BinTree A

-- Size of a tree (number of nodes)
mutual
  size : {A : Set} -> Tree A -> Nat
  size (node _ kids) = succ (sizeForest kids)

  sizeForest : {A : Set} -> List (Tree A) -> Nat
  sizeForest [] = zero
  sizeForest (t :: ts) = size t + sizeForest ts

-- Size of binary tree
binSize : {A : Set} -> BinTree A -> Nat
binSize leaf = zero
binSize (branch _ l r) = succ (binSize l + binSize r)

-- Number of edges in a tree
mutual
  edges : {A : Set} -> Tree A -> Nat
  edges (node _ kids) = edgesForest kids + length kids

  edgesForest : {A : Set} -> List (Tree A) -> Nat
  edgesForest [] = zero
  edgesForest (t :: ts) = edges t + edgesForest ts

-- Height of a tree
mutual
  height : {A : Set} -> Tree A -> Nat
  height (node _ []) = zero
  height (node _ kids) = succ (maxHeight kids)

  maxHeight : {A : Set} -> List (Tree A) -> Nat
  maxHeight [] = zero
  maxHeight (t :: ts) = max (height t) (maxHeight ts)

-- Height of binary tree
binHeight : {A : Set} -> BinTree A -> Nat
binHeight leaf = zero
binHeight (branch _ l r) = succ (max (binHeight l) (binHeight r))

-- Number of leaves
mutual
  leaves : {A : Set} -> Tree A -> Nat
  leaves (node _ []) = one
  leaves (node _ kids) = leavesForest kids

  leavesForest : {A : Set} -> List (Tree A) -> Nat
  leavesForest [] = zero
  leavesForest (t :: ts) = leaves t + leavesForest ts

-- Binary tree leaves
binLeaves : {A : Set} -> BinTree A -> Nat
binLeaves leaf = one
binLeaves (branch _ l r) = binLeaves l + binLeaves r

-- ============================================
-- TREE PROPERTIES
-- ============================================

-- Key theorem: |E| = |V| - 1 for trees
postulate
  edgesSize : {A : Set} -> (t : Tree A) -> Eq (edges t) (size t - one)

-- Full binary tree: every node has 0 or 2 children
FullBinTree : {A : Set} -> BinTree A -> Set
FullBinTree leaf = Unit
FullBinTree (branch _ leaf leaf) = Unit
FullBinTree (branch _ leaf (branch _ _ _)) = Empty  -- not full
FullBinTree (branch _ (branch _ _ _) leaf) = Empty  -- not full
FullBinTree (branch _ l@(branch _ _ _) r@(branch _ _ _)) = Pair (FullBinTree l) (FullBinTree r)

-- Complete binary tree: all levels full except possibly last
postulate
  CompleteBinTree : {A : Set} -> BinTree A -> Set

-- Perfect binary tree: all internal nodes have 2 children, all leaves at same depth
postulate
  PerfectBinTree : {A : Set} -> BinTree A -> Set

-- m-ary tree: each node has at most m children
postulate
  MAryTree : Nat -> Set -> Set

-- Leaf count in full binary tree
postulate
  fullTreeLeaves : {A : Set} (t : BinTree A) -> FullBinTree t ->
    Sigma Nat (\n -> Eq (binLeaves t) (succ n))

-- ============================================
-- TREE TRAVERSALS
-- ============================================

-- Preorder traversal of binary tree
preorder : {A : Set} -> BinTree A -> List A
preorder leaf = []
preorder (branch x l r) = x :: (preorder l ++ preorder r)

-- Inorder traversal of binary tree
inorder : {A : Set} -> BinTree A -> List A
inorder leaf = []
inorder (branch x l r) = inorder l ++ (x :: inorder r)

-- Postorder traversal of binary tree
postorderT : {A : Set} -> BinTree A -> List A
postorderT leaf = []
postorderT (branch x l r) = postorderT l ++ postorderT r ++ (x :: [])

-- Level-order traversal (BFS)
postulate
  levelOrder : {A : Set} -> BinTree A -> List A

-- ============================================
-- SPANNING TREES
-- ============================================

-- A spanning tree of a graph includes all vertices
postulate
  SpanningTree : Set -> Set

-- Every connected graph has a spanning tree
postulate
  connectedHasSpanningTree : Set

-- Number of spanning trees in K_n is n^(n-2) (Cayley's formula)
postulate
  cayleyFormula : (n : Nat) -> Nat

-- ============================================
-- SHORTEST PATH ALGORITHMS
-- ============================================

-- Weighted edge
WeightedEdge : Set -> Set
WeightedEdge V = Pair (Pair V V) Nat

-- Weighted graph as list of edges
WeightedGraphList : Set -> Set
WeightedGraphList V = List (WeightedEdge V)

-- Distance (possibly infinite)
data Distance : Set where
  finite : Nat -> Distance
  infinity : Distance

-- Compare distances
distLeq : Distance -> Distance -> Bool
distLeq infinity _ = false
distLeq (finite _) infinity = true
distLeq (finite m) (finite n) = m <=? n

-- Add distances
distAdd : Distance -> Distance -> Distance
distAdd infinity _ = infinity
distAdd _ infinity = infinity
distAdd (finite m) (finite n) = finite (m + n)

-- Dijkstra's algorithm (abstract specification)
postulate
  dijkstra : {V : Set} -> WeightedGraphList V -> V -> V -> Distance

  -- Correctness: returns shortest path distance
  dijkstraCorrect : {V : Set} (g : WeightedGraphList V) (s t : V) ->
    Set  -- dijkstra g s t is the minimum distance from s to t

-- Bellman-Ford (handles negative weights)
postulate
  bellmanFord : {V : Set} -> WeightedGraphList V -> V -> V -> Distance

-- Floyd-Warshall (all pairs shortest paths)
postulate
  floydWarshall : {V : Set} -> WeightedGraphList V -> V -> V -> Distance

-- ============================================
-- MINIMUM SPANNING TREES
-- ============================================

-- MST: spanning tree with minimum total weight
postulate
  MinimumSpanningTree : {V : Set} -> WeightedGraphList V -> Set

-- Kruskal's algorithm
postulate
  kruskal : {V : Set} -> WeightedGraphList V -> WeightedGraphList V

-- Prim's algorithm
postulate
  prim : {V : Set} -> WeightedGraphList V -> V -> WeightedGraphList V

-- Cut property: lightest edge across any cut is in MST
postulate
  cutProperty : {V : Set} -> WeightedGraphList V -> Set
