{-# OPTIONS --type-in-type #-}

module Week03_RelationsMod where

open import Common

Rel : Set -> Set
Rel A = A -> A -> Set

Reflexive : {A : Set} -> Rel A -> Set
Reflexive {A} R = (x : A) -> R x x

Symmetric : {A : Set} -> Rel A -> Set
Symmetric {A} R = (x y : A) -> R x y -> R y x

Transitive : {A : Set} -> Rel A -> Set
Transitive {A} R = (x y z : A) -> R x y -> R y z -> R x z

Equivalence : {A : Set} -> Rel A -> Set
Equivalence R = Pair (Reflexive R) (Pair (Symmetric R) (Transitive R))

eqRefl : {A : Set} -> Reflexive (Eq {A})
eqRefl x = refl

eqSym : {A : Set} -> Symmetric (Eq {A})
eqSym x y p = sym p

eqTrans : {A : Set} -> Transitive (Eq {A})
eqTrans x y z p q = trans p q

eqEquivalence : {A : Set} -> Equivalence (Eq {A})
eqEquivalence = pair eqRefl (pair eqSym eqTrans)

CongruentMod : Nat -> Nat -> Nat -> Set
CongruentMod n a b = Sigma Nat (\k -> Eq (a + (k * n)) b)

congRefl : (n a : Nat) -> CongruentMod n a a
congRefl n a = sigma zero (addZeroRight a)
