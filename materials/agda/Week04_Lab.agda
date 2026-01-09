{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week04_Lab where

open import Common
open import Week04_CountingProb1

-- Lab focus: counting rules and small computations.

exercise-countComplementZero : (sampleSize : Nat) ->
  Eq (countComplement sampleSize zero) sampleSize
exercise-countComplementZero sampleSize = {!!}

exercise-countSubsetsZero : Eq (countSubsets zero) one
exercise-countSubsetsZero = {!!}

exercise-factorialTwo : Eq (Factorial (succ (succ zero))) (succ (succ zero))
exercise-factorialTwo = {!!}
