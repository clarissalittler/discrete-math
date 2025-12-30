{-# OPTIONS --type-in-type #-}

module Week06_ExpectationGraphs where

open import Common

Weighted : Set
Weighted = List (Pair Nat Nat)

weightedSum : Weighted -> Nat
weightedSum xs = sum (map (\p -> fst p * snd p) xs)

totalWeight : Weighted -> Nat
totalWeight xs = sum (map snd xs)

expectedValueNumerator : Weighted -> Nat
expectedValueNumerator = weightedSum

record Graph : Set where
  field
    V : Set
    E : V -> V -> Set

postulate
  vertices : (g : Graph) -> List (Graph.V g)
  degree : (g : Graph) -> Graph.V g -> Nat
  edges : (g : Graph) -> Nat
  handshake : (g : Graph) ->
    Eq (sum (map (degree g) (vertices g))) (succ (succ zero) * edges g)
