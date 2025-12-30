{-# OPTIONS --type-in-type #-}

module Week10_Efficiency where

open import Common

BigO : (Nat -> Nat) -> (Nat -> Nat) -> Set
BigO f g = Sigma Nat (\c -> Sigma Nat (\n0 -> (n : Nat) -> Leq n0 n -> Leq (f n) (c * g n)))

BigOmega : (Nat -> Nat) -> (Nat -> Nat) -> Set
BigOmega f g = BigO g f

BigTheta : (Nat -> Nat) -> (Nat -> Nat) -> Set
BigTheta f g = Pair (BigO f g) (BigOmega f g)

bigORefl : (f : Nat -> Nat) -> BigO f f
bigORefl f = sigma one (sigma zero proof)
  where
    proof : (n : Nat) -> Leq zero n -> Leq (f n) (one * f n)
    proof n _ = leqEq (sym (mulOneLeft (f n)))
