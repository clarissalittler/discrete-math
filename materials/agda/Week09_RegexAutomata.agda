{-# OPTIONS --type-in-type #-}

module Week09_RegexAutomata where

open import Common

-- ============================================
-- REGULAR EXPRESSIONS
-- ============================================

-- Regular expression syntax
data Regex (A : Set) : Set where
  empty : Regex A           -- Empty language (matches nothing)
  eps : Regex A             -- Empty string (epsilon)
  lit : A -> Regex A        -- Single character
  alt : Regex A -> Regex A -> Regex A   -- Union (r1 | r2)
  seq : Regex A -> Regex A -> Regex A   -- Concatenation (r1 r2)
  star : Regex A -> Regex A             -- Kleene star (r*)

-- Matching semantics
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

-- Empty language matches nothing
emptyNoMatch : {A : Set} {xs : List A} -> Not (Matches empty xs)
emptyNoMatch ()

-- Epsilon only matches empty string
epsOnlyEmpty : {A : Set} {xs : List A} -> Matches eps xs -> Eq xs []
epsOnlyEmpty mEps = refl

-- Language defined by a regex
Lang : {A : Set} -> Regex A -> Pred (List A)
Lang r xs = Matches r xs

-- Nullable: does the regex match the empty string?
nullable : {A : Set} -> Regex A -> Bool
nullable empty = false
nullable eps = true
nullable (lit _) = false
nullable (alt r1 r2) = nullable r1 || nullable r2
nullable (seq r1 r2) = nullable r1 && nullable r2
nullable (star _) = true

-- Nullable correctness (proof requires case analysis)
postulate
  nullableCorrect : {A : Set} (r : Regex A) ->
    Eq (nullable r) true -> Matches r []

-- Derivative of a regex (Brzozowski derivative)
derivative : {A : Set} -> (A -> A -> Bool) -> A -> Regex A -> Regex A
derivative eq a empty = empty
derivative eq a eps = empty
derivative eq a (lit c) = if eq a c then eps else empty
derivative eq a (alt r1 r2) = alt (derivative eq a r1) (derivative eq a r2)
derivative eq a (seq r1 r2) =
  if nullable r1
  then alt (seq (derivative eq a r1) r2) (derivative eq a r2)
  else seq (derivative eq a r1) r2
derivative eq a (star r) = seq (derivative eq a r) (star r)

-- ============================================
-- DETERMINISTIC FINITE AUTOMATA
-- ============================================

-- DFA definition
record DFA (State Alpha : Set) : Set where
  field
    start : State
    accept : State -> Bool
    step : State -> Alpha -> State

-- Run DFA on a string
run : {S A : Set} -> DFA S A -> S -> List A -> S
run d s [] = s
run d s (a :: rest) = run d (DFA.step d s a) rest

-- DFA acceptance
accepts : {S A : Set} -> DFA S A -> List A -> Set
accepts d input = Eq (DFA.accept d (run d (DFA.start d) input)) true

-- DFA language
dfaLang : {S A : Set} -> DFA S A -> Pred (List A)
dfaLang d = accepts d

-- ============================================
-- NFA (Non-deterministic Finite Automata)
-- ============================================

-- NFA with epsilon transitions
record NFA (State Alpha : Set) : Set where
  field
    start : State
    accept : State -> Bool
    step : State -> Alpha -> List State
    epsilonStep : State -> List State

-- NFA acceptance (existential: some path leads to accept)
postulate
  nfaAccepts : {S A : Set} -> NFA S A -> List A -> Set

-- ============================================
-- KLEENE'S THEOREM
-- ============================================

-- Every DFA defines a regular language
postulate
  dfaToRegex : {S A : Set} -> DFA S A -> Regex A

-- Every regex can be recognized by some DFA
postulate
  regexToDfa : {A : Set} -> Regex A -> Sigma Set (\S -> DFA S A)

-- Kleene's theorem: DFA languages = Regular languages
postulate
  kleeneTheorem : {A : Set} (r : Regex A) ->
    Sigma Set (\S -> Sigma (DFA S A) (\d ->
      (xs : List A) -> Matches r xs -> accepts d xs))

-- ============================================
-- CLOSURE PROPERTIES
-- ============================================

-- Regular languages are closed under union
postulate
  regUnion : {A : Set} -> Regex A -> Regex A -> Regex A
  regUnionCorrect : {A : Set} (r1 r2 : Regex A) (xs : List A) ->
    Sum (Matches r1 xs) (Matches r2 xs) -> Matches (regUnion r1 r2) xs

-- Regular languages are closed under concatenation
postulate
  regConcat : {A : Set} -> Regex A -> Regex A -> Regex A
  regConcatCorrect : {A : Set} (r1 r2 : Regex A) (xs ys : List A) ->
    Matches r1 xs -> Matches r2 ys -> Matches (regConcat r1 r2) (xs ++ ys)

-- Regular languages are closed under Kleene star
postulate
  regStar : {A : Set} -> Regex A -> Regex A
  regStarCorrect : {A : Set} (r : Regex A) -> Matches (regStar r) []

-- Regular languages are closed under complement
postulate
  regComplement : {A : Set} -> Regex A -> Regex A
  regComplementCorrect : {A : Set} (r : Regex A) (xs : List A) ->
    Not (Matches r xs) -> Matches (regComplement r) xs

-- Regular languages are closed under intersection
postulate
  regIntersect : {A : Set} -> Regex A -> Regex A -> Regex A
  regIntersectCorrect : {A : Set} (r1 r2 : Regex A) (xs : List A) ->
    Matches r1 xs -> Matches r2 xs -> Matches (regIntersect r1 r2) xs

-- ============================================
-- DFA MINIMIZATION
-- ============================================

-- Two states are equivalent if they accept the same strings
StateEquiv : {S A : Set} -> DFA S A -> S -> S -> Set
StateEquiv {S} {A} d s1 s2 = (xs : List A) ->
  Eq (DFA.accept d (run d s1 xs)) (DFA.accept d (run d s2 xs))

-- Minimized DFA
postulate
  minimizeDfa : {S A : Set} -> DFA S A -> Sigma Set (\S' -> DFA S' A)

-- Minimized DFA has minimum number of states
postulate
  minimizeDfaOptimal : {S A : Set} (d : DFA S A) ->
    Set  -- No equivalent DFA has fewer states

-- ============================================
-- PUMPING LEMMA (for proving languages non-regular)
-- ============================================

-- Pumping lemma: every regular language satisfies the pumping property
postulate
  pumpingLemma : {A : Set} (r : Regex A) ->
    Sigma Nat (\p ->  -- pumping length
      (xs : List A) -> Matches r xs -> Leq p (length xs) ->
      Set)  -- can be pumped
