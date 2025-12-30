{-# OPTIONS --type-in-type #-}

module Week01_SetTheory where

open import Common

_⊆_ : {A : Set} -> Pred A -> Pred A -> Set
_⊆_ {A} P Q = (x : A) -> P x -> Q x

SetEq : {A : Set} -> Pred A -> Pred A -> Set
SetEq P Q = Pair (P ⊆ Q) (Q ⊆ P)

_∩_ : {A : Set} -> Pred A -> Pred A -> Pred A
(P ∩ Q) x = Pair (P x) (Q x)

_∪_ : {A : Set} -> Pred A -> Pred A -> Pred A
(P ∪ Q) x = Sum (P x) (Q x)

Compl : {A : Set} -> Pred A -> Pred A
Compl P x = Not (P x)

subsetRefl : {A : Set} (P : Pred A) -> P ⊆ P
subsetRefl P x px = px

subsetTrans : {A : Set} {P Q R : Pred A} -> P ⊆ Q -> Q ⊆ R -> P ⊆ R
subsetTrans pq qr x px = qr x (pq x px)

deMorganUnion : {A : Set} (P Q : Pred A) -> SetEq (Compl (P ∪ Q)) (Compl P ∩ Compl Q)
deMorganUnion P Q = pair left right
  where
    left : Compl (P ∪ Q) ⊆ (Compl P ∩ Compl Q)
    left x notPQ = pair (\px -> notPQ (inl px)) (\qx -> notPQ (inr qx))

    right : (Compl P ∩ Compl Q) ⊆ Compl (P ∪ Q)
    right x (pair notP notQ) (inl px) = notP px
    right x (pair notP notQ) (inr qx) = notQ qx
