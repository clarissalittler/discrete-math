{-# OPTIONS --type-in-type --allow-unsolved-metas #-}

module Week09_Lab where

open import Common
open import Week09_RegexAutomata

-- Lab focus: regex semantics and DFA runs.

exercise-nullableStar : {A : Set} (r : Regex A) -> Eq (nullable (star r)) true
exercise-nullableStar r = {!!}

exercise-runNil : {S A : Set} (d : DFA S A) (s : S) -> Eq (run d s []) s
exercise-runNil d s = {!!}

exercise-litMatches : {A : Set} (a : A) -> Matches (lit a) (a :: [])
exercise-litMatches a = {!!}

exercise-nullableEps : {A : Set} -> Eq (nullable (eps {A})) true
exercise-nullableEps = {!!}
