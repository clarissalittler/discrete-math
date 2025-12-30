{-# OPTIONS --type-in-type #-}

module Week05_CountingProb2 where

open import Common

fact : Nat -> Nat
fact zero = one
fact (succ n) = succ n * fact n

choose : Nat -> Nat -> Nat
choose n zero = one
choose zero (succ k) = zero
choose (succ n) (succ k) = choose n (succ k) + choose n k

chooseZero : (n : Nat) -> Eq (choose n zero) one
chooseZero n = refl

pascal : (n k : Nat) -> Eq (choose (succ n) (succ k)) (choose n (succ k) + choose n k)
pascal n k = refl
