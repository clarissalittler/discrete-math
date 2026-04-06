{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week02_Lab where

open import Common
open import Week02_Functions hiding (exercise-preimageSubset)
open import Week01_SetTheory using (_⊆_)

-- Lab focus: composition, inverses, and preimages.

exercise-composeIdLeft : {A B : Set} (f : A -> B) (x : A) ->
  Eq ((id ∘ f) x) (f x)
exercise-composeIdLeft f x = {!!}

exercise-leftInverseInjective : {A B : Set} {f : A -> B} {g : B -> A} ->
  LeftInverse g f -> Injective f
exercise-leftInverseInjective left x y fx=fy = {!!}

exercise-preimageSubset : {A B : Set} (f : A -> B) {P Q : Pred B} ->
  P ⊆ Q -> Preimage f P ⊆ Preimage f Q
exercise-preimageSubset f pq x pfx = {!!}

exercise-composeAssoc : {A B C D : Set} {f : A -> B} {g : B -> C} {h : C -> D} ->
  (x : A) -> Eq (((h ∘ g) ∘ f) x) ((h ∘ (g ∘ f)) x)
exercise-composeAssoc x = {!!}
