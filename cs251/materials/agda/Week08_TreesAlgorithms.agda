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

-- ============================================
-- FOLDS AND CATAMORPHISMS
-- ============================================

{-
  A fold (catamorphism) is a structured way to process a recursive data type.
  For binary trees:
    fold : (A -> B -> B -> B) -> B -> BinTree A -> B

  This captures the pattern:
  - Replace `leaf` with the base value
  - Replace `branch x left right` with `f x (fold left) (fold right)`

  Many tree operations can be expressed as folds!
-}

-- Generic fold for binary trees
binFold : {A B : Set} -> (A -> B -> B -> B) -> B -> BinTree A -> B
binFold f z leaf = z
binFold f z (branch x left right) = f x (binFold f z left) (binFold f z right)

-- Size as a fold
sizeAsFold : {A : Set} -> BinTree A -> Nat
sizeAsFold = binFold (\_ l r -> succ (l + r)) zero

-- Height as a fold
heightAsFold : {A : Set} -> BinTree A -> Nat
heightAsFold = binFold (\_ l r -> succ (max l r)) zero

-- Sum of all elements (for Nat trees)
sumTree : BinTree Nat -> Nat
sumTree = binFold (\x l r -> x + l + r) zero

-- Flatten to list (inorder) as a fold
flattenInorder : {A : Set} -> BinTree A -> List A
flattenInorder = binFold (\x l r -> l ++ (x :: r)) []

-- Mirror/reflect a tree
mirror : {A : Set} -> BinTree A -> BinTree A
mirror = binFold (\x l r -> branch x r l) leaf

-- Map as a fold
mapTree : {A B : Set} -> (A -> B) -> BinTree A -> BinTree B
mapTree f = binFold (\x l r -> branch (f x) l r) leaf

-- ============================================
-- FOLD FUSION AND LAWS
-- ============================================

{-
  Key insight: many tree operations satisfy algebraic laws
  because they're defined as folds.

  Fusion law: if h is a homomorphism, then
    h . fold f z = fold g (h z)
  where g x (h l) (h r) = h (f x l r)
-}

-- Fold with leaf produces identity
postulate
  foldLeaf : {A : Set} (t : BinTree A) ->
    Eq (binFold branch leaf t) t

-- Mirror is an involution: mirror (mirror t) = t
postulate
  mirrorInvolution : {A : Set} (t : BinTree A) ->
    Eq (mirror (mirror t)) t

-- Size equals length of flattened list
postulate
  sizeIsLength : {A : Set} (t : BinTree A) ->
    Eq (sizeAsFold t) (length (flattenInorder t))

-- ============================================
-- ROSE TREE FOLDS (General Trees)
-- ============================================

-- Fold for general trees (rose trees)
mutual
  treeFold : {A B : Set} -> (A -> List B -> B) -> Tree A -> B
  treeFold f (node x children) = f x (forestFold f children)

  forestFold : {A B : Set} -> (A -> List B -> B) -> List (Tree A) -> List B
  forestFold f [] = []
  forestFold f (t :: ts) = treeFold f t :: forestFold f ts

-- Tree size as a fold
treeSizeAsFold : {A : Set} -> Tree A -> Nat
treeSizeAsFold = treeFold (\_ childSizes -> succ (sum childSizes))

-- ============================================
-- EXERCISES
-- ============================================

{-
  EXERCISE 1: Prove that size computed directly equals sizeAsFold
-}
postulate
  exercise-sizeEquiv : {A : Set} (t : BinTree A) ->
    Eq (binSize t) (sizeAsFold t)

{-
  EXERCISE 2: Prove that height computed directly equals heightAsFold
-}
postulate
  exercise-heightEquiv : {A : Set} (t : BinTree A) ->
    Eq (binHeight t) (heightAsFold t)

{-
  EXERCISE 3: Express "count leaves" as a fold
-}
countLeavesAsFold : {A : Set} -> BinTree A -> Nat
countLeavesAsFold = binFold (\_ l r -> l + r) one

-- Verify it equals binLeaves
postulate
  exercise-leavesEquiv : {A : Set} (t : BinTree A) ->
    Eq (binLeaves t) (countLeavesAsFold t)

{-
  EXERCISE 4: Express "all elements satisfy predicate" as a fold
-}
allTree : {A : Set} -> (A -> Bool) -> BinTree A -> Bool
allTree p = binFold (\x l r -> p x && l && r) true

{-
  EXERCISE 5: Express "exists element satisfying predicate" as a fold
-}
anyTree : {A : Set} -> (A -> Bool) -> BinTree A -> Bool
anyTree p = binFold (\x l r -> p x || l || r) false

{-
  EXERCISE 6: Prove that map preserves tree structure
  mapTree id = id
-}
postulate
  exercise-mapId : {A : Set} (t : BinTree A) ->
    Eq (mapTree (\x -> x) t) t

{-
  EXERCISE 7: Prove that map composes
  mapTree (f ∘ g) = mapTree f ∘ mapTree g
-}
postulate
  exercise-mapCompose : {A B C : Set} (f : B -> C) (g : A -> B) (t : BinTree A) ->
    Eq (mapTree (\x -> f (g x)) t) (mapTree f (mapTree g t))

{-
  EXERCISE 8: Express preorder traversal as a fold
-}
preorderAsFold : {A : Set} -> BinTree A -> List A
preorderAsFold = binFold (\x l r -> x :: (l ++ r)) []

{-
  EXERCISE 9: Express postorder traversal as a fold
-}
postorderAsFold : {A : Set} -> BinTree A -> List A
postorderAsFold = binFold (\x l r -> l ++ r ++ (x :: [])) []

{-
  EXERCISE 10: The fusion law example
  Prove: sum (map (λx → x + 1) list) = length list + sum list
  (This is actually a list fold fusion, but illustrates the principle)
-}
postulate
  exercise-foldFusion : (xs : List Nat) ->
    Eq (sum (map succ xs)) (length xs + sum xs)
