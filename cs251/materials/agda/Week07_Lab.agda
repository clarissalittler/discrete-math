{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week07_Lab where

open import Common
open import Week07_GraphTheoryI

-- Lab focus: walks and basic graph properties.

exercise-walkLengthSingle : {n : Nat} {g : MatrixGraph n} {v : Fin n} ->
  Eq (walkLength (single {g = g} {v = v})) zero
exercise-walkLengthSingle = {!!}

exercise-walkStartSingle : {n : Nat} {g : MatrixGraph n} {v : Fin n} ->
  Eq (walkStart (single {g = g} {v = v})) v
exercise-walkStartSingle = {!!}

exercise-walkLengthStep : {n : Nat} {g : MatrixGraph n} {u v : Fin n} {rest : List (Fin n)} ->
  (e : Edge g u v) -> (w : Walk g (v :: rest)) ->
  Eq (walkLength (step e w)) (succ (walkLength w))
exercise-walkLengthStep e w = {!!}
