{-# OPTIONS --type-in-type #-}

module Week07_GraphTheoryI where

open import Common

record MatrixGraph (n : Nat) : Set where
  field
    adj : Fin n -> Fin n -> Bool

Edge : {n : Nat} -> MatrixGraph n -> Fin n -> Fin n -> Set
Edge g u v = Eq (MatrixGraph.adj g u v) true

data Walk {n : Nat} (g : MatrixGraph n) : List (Fin n) -> Set where
  single : {v : Fin n} -> Walk g (v :: [])
  step : {u v : Fin n} {rest : List (Fin n)} ->
    Edge g u v -> Walk g (v :: rest) -> Walk g (u :: v :: rest)

postulate
  EulerTrail : {n : Nat} -> MatrixGraph n -> List (Fin n) -> Set
  Isomorphic : {n m : Nat} -> MatrixGraph n -> MatrixGraph m -> Set
