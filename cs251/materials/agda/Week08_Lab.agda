{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week08_Lab where

open import Common
open import Week08_TreesAlgorithms

-- Lab focus: tree sizes and traversals.

exercise-binSizeLeaf : {A : Set} -> Eq (binSize (leaf {A})) zero
exercise-binSizeLeaf = {!!}

exercise-binLeavesLeaf : {A : Set} -> Eq (binLeaves (leaf {A})) one
exercise-binLeavesLeaf = {!!}

exercise-preorderLeaf : {A : Set} -> Eq (preorder (leaf {A})) []
exercise-preorderLeaf = {!!}

exercise-binHeightLeaf : {A : Set} -> Eq (binHeight (leaf {A})) zero
exercise-binHeightLeaf = {!!}
