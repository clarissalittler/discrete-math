{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week06_Lab where

open import Common
open import Week06_ExpectationGraphs

-- Lab focus: expectation basics and simple list computations.

exercise-weightedSumSingle : (v w : Nat) ->
  Eq (weightedSum (pair v w :: [])) (v * w)
exercise-weightedSumSingle v w = {!!}

exercise-totalWeightCons : (v w : Nat) (xs : Weighted) ->
  Eq (totalWeight (pair v w :: xs)) (w + totalWeight xs)
exercise-totalWeightCons v w xs = {!!}

exercise-indicatorTrue : {S : Set} (s : S) -> Eq (indicator (\_ -> true) s) one
exercise-indicatorTrue s = {!!}
