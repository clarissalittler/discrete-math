{-# OPTIONS --type-in-type #-}

module Week09_RegexAutomata where

open import Common

data Regex (A : Set) : Set where
  empty : Regex A
  eps : Regex A
  lit : A -> Regex A
  alt : Regex A -> Regex A -> Regex A
  seq : Regex A -> Regex A -> Regex A
  star : Regex A -> Regex A

data Matches {A : Set} : Regex A -> List A -> Set where
  mEps : Matches eps []
  mLit : (a : A) -> Matches (lit a) (a :: [])
  mAltL : {r1 r2 : Regex A} {xs : List A} -> Matches r1 xs -> Matches (alt r1 r2) xs
  mAltR : {r1 r2 : Regex A} {xs : List A} -> Matches r2 xs -> Matches (alt r1 r2) xs
  mSeq : {r1 r2 : Regex A} {xs ys : List A} ->
    Matches r1 xs -> Matches r2 ys -> Matches (seq r1 r2) (xs ++ ys)
  mStar0 : {r : Regex A} -> Matches (star r) []
  mStarStep : {r : Regex A} {xs ys : List A} ->
    Matches r xs -> Matches (star r) ys -> Matches (star r) (xs ++ ys)

record DFA (State Alpha : Set) : Set where
  field
    start : State
    accept : State -> Bool
    step : State -> Alpha -> State

run : {S A : Set} -> DFA S A -> S -> List A -> S
run d s [] = s
run d s (a :: rest) = run d (DFA.step d s a) rest

accepts : {S A : Set} -> DFA S A -> List A -> Set
accepts d input = Eq (DFA.accept d (run d (DFA.start d) input)) true
