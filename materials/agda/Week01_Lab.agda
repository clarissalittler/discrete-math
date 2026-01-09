{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week01_Lab where

open import Common
open import Week01_SetTheory hiding (exercise-subsetTrans; exercise-emptySubset; exercise-unionMono)

-- Lab focus: sets as predicates, subset reasoning, union/intersection.

exercise-subsetTrans : {A : Set} {P Q R : Pred A} -> P ⊆ Q -> Q ⊆ R -> P ⊆ R
exercise-subsetTrans pq qr x px = {!!}

exercise-emptySubset : {A : Set} (P : Pred A) -> EmptySet ⊆ P
exercise-emptySubset P x e = {!!}

exercise-unionMono : {A : Set} {P P' Q Q' : Pred A} ->
  P ⊆ P' -> Q ⊆ Q' -> (P ∪ Q) ⊆ (P' ∪ Q')
exercise-unionMono pp' qq' x pq = {!!}
