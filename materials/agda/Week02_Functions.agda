{-# OPTIONS --type-in-type #-}

module Week02_Functions where

open import Common

Compose : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
Compose g f x = g (f x)

Injective : {A B : Set} -> (A -> B) -> Set
Injective {A} f = (x y : A) -> Eq (f x) (f y) -> Eq x y

Surjective : {A B : Set} -> (A -> B) -> Set
Surjective {A} {B} f = (y : B) -> Sigma A (\x -> Eq (f x) y)

Bijective : {A B : Set} -> (A -> B) -> Set
Bijective f = Pair (Injective f) (Surjective f)

LeftInverse : {A B : Set} -> (B -> A) -> (A -> B) -> Set
LeftInverse {A} g f = (x : A) -> Eq (g (f x)) x

leftInverseInjective : {A B : Set} {f : A -> B} {g : B -> A} ->
  LeftInverse g f -> Injective f
leftInverseInjective {g = g} left x y fx=fy =
  trans (sym (left x)) (trans (cong g fx=fy) (left y))

composeInjective : {A B C : Set} {f : A -> B} {g : B -> C} ->
  Injective f -> Injective g -> Injective (Compose g f)
composeInjective {f = f} {g = g} injF injG x y eq =
  injF x y (injG (f x) (f y) eq)

composeSurjective : {A B C : Set} {f : A -> B} {g : B -> C} ->
  Surjective f -> Surjective g -> Surjective (Compose g f)
composeSurjective {f = f} {g = g} surF surG z with surG z
... | sigma y gy with surF y
... | sigma x fx = sigma x (trans (cong g fx) gy)
