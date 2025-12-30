{-# OPTIONS --type-in-type #-}

module Week08_TreesAlgorithms where

open import Common

data Tree (A : Set) : Set where
  node : A -> List (Tree A) -> Tree A

mutual
  size : {A : Set} -> Tree A -> Nat
  size (node _ kids) = succ (sizeForest kids)

  sizeForest : {A : Set} -> List (Tree A) -> Nat
  sizeForest [] = zero
  sizeForest (t :: ts) = size t + sizeForest ts

mutual
  edges : {A : Set} -> Tree A -> Nat
  edges (node _ kids) = edgesForest kids + length kids

  edgesForest : {A : Set} -> List (Tree A) -> Nat
  edgesForest [] = zero
  edgesForest (t :: ts) = edges t + edgesForest ts

postulate
  edgesSize : {A : Set} -> (t : Tree A) -> Eq (edges t) (size t - one)
  spanningTree : {A : Set} -> Set
  shortestPath : {A : Set} -> Set
