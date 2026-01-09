{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week05_Lab where

open import Common
open import Week05_CountingProb2 hiding (exercise-chooseZero; exercise-choose52)

-- Lab focus: binomial coefficients and Pascal identity.

exercise-chooseZero : (n : Nat) -> Eq (choose n zero) one
exercise-chooseZero n = {!!}

exercise-pascal : (n k : Nat) ->
  Eq (choose (succ n) (succ k)) (choose n (succ k) + choose n k)
exercise-pascal n k = {!!}

exercise-choose52 : Eq (choose (succ (succ (succ (succ (succ zero)))))
                              (succ (succ zero)))
                      (succ (succ (succ (succ (succ
                       (succ (succ (succ (succ (succ zero))))))))))
exercise-choose52 = {!!}
