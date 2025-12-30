{-# OPTIONS --type-in-type #-}

module Week04_CountingProb1 where

open import Common

Event : Set -> Set
Event A = Pred A

Disjoint : {A : Set} -> Event A -> Event A -> Set
Disjoint {A} P Q = (x : A) -> P x -> Q x -> Empty

countProduct : Nat -> Nat -> Nat
countProduct m n = m * n

countSum : Nat -> Nat -> Nat
countSum m n = m + n

countUnion : Nat -> Nat -> Nat -> Nat
countUnion countA countB inter = (countA + countB) - inter

postulate
  pigeonhole : (pigeons holes : Nat) -> Leq (succ holes) pigeons -> Set
