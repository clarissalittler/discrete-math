{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week03_Lab where

open import Common
open import Week03_RelationsMod

-- Lab focus: relations, closures, and modular equivalence.

exercise-reflClosureRefl : {A : Set} {R : Rel A} -> Reflexive (ReflClosure R)
exercise-reflClosureRefl x = {!!}

exercise-symClosureSym : {A : Set} {R : Rel A} -> Symmetric (SymClosure R)
exercise-symClosureSym x y r = {!!}

exercise-modEqSym : {n a b : Nat} -> ModEq n a b -> ModEq n b a
exercise-modEqSym proof = {!!}

exercise-modEqRefl : (n a : Nat) -> ModEq n a a
exercise-modEqRefl n a = {!!}
