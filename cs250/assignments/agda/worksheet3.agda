module worksheet3 where

{- old stuff that I'm going to include here so it's all in one place -}

data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a

infixl 1 _≡_
{-# BUILTIN EQUALITY _≡_ #-}

data Bool : Set where
 True : Bool
 False : Bool

_∧_ : Bool -> Bool -> Bool
True ∧ True = True
True ∧ False = False
False ∧ True = False
False ∧ False = False

infixl 8 _∧_

_∨_ : Bool -> Bool -> Bool
True ∨ True = True
True ∨ False = True
False ∨ True = True
False ∨ False = False

infixl 5 _∨_

¬ : Bool -> Bool
¬ True = False
¬ False = True

_|->_ : Bool -> Bool -> Bool
True  |-> True = True
True  |-> False = False
False |-> b = True

infixr 2 _|->_


{-

  The point of this worksheet is to connect the /semantics/ of propositional logic, which you did in the last worksheet, with the /syntax/ of propositional logic and the rules of inference you learned (things like generalization, specialization, mp, &c.)

  Like worksheet 2 a lot of this is just you getting used to the syntax and reading Agda programs so that you can understand what's going on. In worksheet 4 and 5 you'll be having to do some more actual inductive calculations that will be a little difficult, ending with writing proofs that are more complicated than just ending with `refl` over and over again!

-}

{-
  The first thing we do is define the inductive set of logical formulae.

This encompasses every formula you can make with the connectives that we learned in the first two weeks of class!

The only thing that might not look familiar with the `atom` constructor, which we use to represent grounded truth and falsity. It just represents the *constants* true and false, hence why it takes a boolean as an argument.

-}

data Formula : Set where
 atom : Bool -> Formula
 _∧f_ : Formula -> Formula -> Formula
 _∨f_ : Formula -> Formula -> Formula
 _|->f_ : Formula -> Formula -> Formula
 ¬f_ : Formula -> Formula

infixr 6 _|->f_
infixl 7 _∧f_
infixl 8 _∨f_
infix  9 ¬f_

-- here's a function that takes a formula as a *syntactic* thing that you'd write
-- and then "evaluates" it
-- this is like a compiler for a really trivial programming language
-- compiling the program to either 1 or 0
-- okay as a warmup finish the rest of this definition I started for you
-- notice the recursive use of eval and the use of the boolean operators defined above!
eval : Formula -> Bool
eval (atom x) = x
eval (p ∧f q) = eval p ∧ eval q
eval (p ∨f q) = {!!}
eval (p |->f q) = {!!}
eval (¬f p) = {!!}

-- Now before we go further we need to establish some properties about our ≡
-- Namely, that it behaves *like* an equality when we need to substitute one equal thing for another
-- in a proposition

-- this type signature says
-- for all sets A and for all predicates P on A, for any a and b ∈ A then if  a ≡ b and P a is true then P b is true  
subst1 : {A : Set} {P : A -> Set} {a b : A} -> a ≡ b -> P a -> P b
subst1 refl p = p -- this is a slightly magical looking proof because we're using the fact that a ≡ b means that, well, a ≡ b. Because of that we can just use the fact that p is a proof that P a and the fact that a and b are *literally the same thing* to say oh look this is also a proof of P b
-- does this seem silly or weird? well that's what happens when we're doing logic from the ground up. we have to encode what it *means* for two things to be equal

-- we also need a slightly different function that will take a predicate on *two* arguments instead, but otherwise it's the same thing
subst2 : {A : Set} {P : A -> A -> Set} {a b c d : A} -> a ≡ b -> c ≡ d -> P a c -> P b d
subst2 refl refl p = p

-- and finally we need a similar thing that says if you feed equal things into functions you get equal results
cong1 : {A B : Set} {a1 a2 : A} -> (f : A -> B) -> a1 ≡ a2 -> f a1 ≡ f a2
cong1 f refl = refl

-- and the version for functions that take two arguments
cong2 : {A B C : Set} {a1 a2 : A} {b1 b2 : B} -> (f : A -> B -> C) -> a1 ≡ a2 -> b1 ≡ b2 -> f a1 b1 ≡ f a2 b2
cong2 f refl refl = refl

-- Revenge of De Morgan!!
-- We define here a program that performs the Of Morgan transformations  
-- we define it recursively on the structure of formulae
-- note though that the first few cases are just about pushing the recursive calls to
-- deMorgan1 down further into the structure of the formula
-- The important case is the one where we have the ¬ in front of another formula
-- we do a *second* layer of recursion in this case in order to apply the rule correctly
deMorgan1 : Formula -> Formula
deMorgan1 (atom x) = atom x
deMorgan1 (f1 ∧f f2) = (deMorgan1 f1) ∧f (deMorgan1 f2)
deMorgan1 (f1 ∨f f2) = (deMorgan1 f1) ∨f (deMorgan1 f2)
deMorgan1 (f1 |->f f2) = (deMorgan1 f1) |->f (deMorgan1 f2)
deMorgan1 (¬f atom True) = atom False
deMorgan1 (¬f atom False) = atom True
deMorgan1 (¬f (f1 ∧f f2)) = {!!} -- fill in this important case, it's the dual to the one below
deMorgan1 (¬f (f1 ∨f f2)) = (¬f (deMorgan1 f1)) ∧f (¬f (deMorgan1 f2))
deMorgan1 (¬f (f1 |->f f2)) = ¬f ((deMorgan1 f1) |->f (deMorgan1 f2))
deMorgan1 (¬f (¬f f)) = ¬f (¬f (deMorgan1 f))

-- this is a lemma that proves that the deMorgan transformation is semantically legitimate
deMorganBool-∧ : (b1 b2 : Bool) -> ¬ (b1 ∧ b2) ≡ (¬ b1) ∨ (¬ b2)
deMorganBool-∧ True True = refl
deMorganBool-∧ True False = refl
deMorganBool-∧ False True = refl
deMorganBool-∧ False False = refl

-- now prove this one the same way
deMorganBool-∨ : (b1 b2 : Bool) -> ¬ (b1 ∨ b2) ≡ (¬ b1) ∧ (¬ b2)
deMorganBool-∨ p q = {!!}


-- one of the important things we can do now is test to make sure that this transformation doesn't change
-- the *meaning* of a formula
-- Write here in the comments: What is your interpretation of the type of the function below?
-- "For every formula f ...?"
-- The proof below is a little too advanced to ask you to do at this point, but try to read it and see what's
-- going on.
-- Basically this proof is a lot like a very simple version of a proof that a compiler can optimize code
-- without changing the meaning of the code! It's actually pretty cool that we can prove correctness of this
-- inside the theorem prover itself!

-- UNCOMMENT THIS BLOCK TO CHECK YOUR WORK
{-
deMorgan-sound : (f : Formula) -> eval f ≡ eval (deMorgan1 f)
deMorgan-sound (atom x) = refl
deMorgan-sound (f1 ∧f f2) = cong2 _∧_ (deMorgan-sound f1) (deMorgan-sound f2)
deMorgan-sound (f1 ∨f f2) = cong2 _∨_ (deMorgan-sound f1) (deMorgan-sound f2)
deMorgan-sound (f1 |->f f2) = cong2 _|->_ (deMorgan-sound f1) (deMorgan-sound f2)
deMorgan-sound (¬f atom True) = refl
deMorgan-sound (¬f atom False) = refl
deMorgan-sound (¬f (f1 ∧f f2)) = helper
 where
  helper : eval (¬f (f1 ∧f f2)) ≡ eval (deMorgan1 (¬f (f1 ∧f f2)))
  helper with deMorgan-sound f1 | deMorgan-sound f2
  ... | p1 | p2 rewrite p1 | p2 = deMorganBool-∧ (eval (deMorgan1 f1)) (eval (deMorgan1 f2))
 
deMorgan-sound (¬f (f1 ∨f f2)) = helper
 where
  helper : eval (¬f (f1 ∨f f2)) ≡ eval (deMorgan1 (¬f (f1 ∨f f2)))
  helper with deMorgan-sound f1 | deMorgan-sound f2
  ... | p1 | p2 rewrite p1 | p2 = deMorganBool-∨ (eval (deMorgan1 f1)) (eval (deMorgan1 f2))
deMorgan-sound (¬f (f1 |->f f2)) = cong1 (λ x → ¬ x) (cong2 _|->_ (deMorgan-sound f1) (deMorgan-sound f2))
deMorgan-sound (¬f (¬f f)) = cong1 (λ x -> ¬ (¬ x)) (deMorgan-sound f)
-}

{-

  The following are a set of helper theorems we need for the proof of soundness: 

  They involve some tricks we'll talk about more in the final worksheet of class
-}

eval-and-helper-1 : (f1 f2 : Formula) -> eval (f1 ∧f f2) ≡ True -> eval f1 ≡ True
eval-and-helper-1 f1 f2 p1 with eval f1 | eval f2 | p1
... | True | True | p1 = refl
... | False | True | ()
... | False | False | ()

eval-and-helper-2 : (f1 f2 : Formula) -> eval (f1 ∧f f2) ≡ True -> eval f2 ≡ True
eval-and-helper-2 f1 f2 p1 with eval f1 | eval f2 | p1
... | True | True | p1 = refl
... | False | True | ()
... | False | False | ()

orTrue-l : (b : Bool) -> True ∨ b ≡ True
orTrue-l True = refl
orTrue-l False = refl

orTrue-r : (b : Bool) -> b ∨ True ≡ True
orTrue-r True = refl
orTrue-r False = refl

-- now for this one there are four arguments but I want you to use cases on b1 and b2 *only*, watch what happens
eval-mp-helper' : (b1 b2 : Bool) -> b1 ≡ True -> (b1 |-> b2) ≡ True -> b2 ≡ True
eval-mp-helper' b1 b2 p1 p2 = {!!}
-- did you notice something weird there? that agda didn't even bother writing the False case?
-- Why do you think that is? Think about what the assumption (True |-> b) ≡ True means when b is False? Is it possible?


doubleNeg-helper : (b : Bool) -> ¬ (¬ b) ≡ True -> b ≡ True
doubleNeg-helper True p = refl

-- Now we can actually encode, in the logic, what it means to prove a theorem in propositional logic
-- This is a inductively defined set *of proof rules*, which means that we can combine them in all the allowed ways
-- to make proofs that a formula is true
-- Read this and talk it out to yourself to see if you can map the rules below to map them to proof rules you learned
-- early in the class

data Provable : Formula -> Set where
  true-is-true : Provable (atom True)
  ∧f-intro : (f1 f2 : Formula) -> Provable f1 -> Provable f2 -> Provable (f1 ∧f f2)
  spec-l : (f1 f2 : Formula) -> Provable (f1 ∧f f2) -> Provable f1
  spec-r : (f1 f2 : Formula) -> Provable (f1 ∧f f2) -> Provable f2
  gen-l : (f1 f2 : Formula)  -> Provable f1 -> Provable (f1 ∨f f2)
  gen-r : (f1 f2 : Formula) -> Provable f2 -> Provable (f1 ∨f f2)
  modus-pony : (f1 f2 : Formula) -> Provable (f1 |->f f2) -> Provable f1 -> Provable f2
  ∨f-by-cases : (f1 f2 f3 : Formula) -> Provable (f1 ∨f f2) -> Provable (f1 |->f f3) -> Provable (f2 |->f f3) → Provable f3
  double-neg : (f : Formula) -> Provable (¬f (¬f f)) -> Provable f
  modus-tolly : (f1 f2 : Formula) -> Provable (¬f f2 |->f ¬f f1) -> Provable (¬f f2) -> Provable (¬f f1)

-- we're not actually going to include proof by contradiction here for some technical reasons
-- the tl;dr is that we have a lot more supplemental theorems and I'm trying to keep this document simple
-- or maybe I'm just lazy
-- you make the call!

-- This datatype and the function below are actually a weird little trick we need for our big proof
-- at the end of this file, where we need to prove to agda that if an or statement is true it really does mean
-- that either the left or right proposition must be equal to true.
-- That seems obvious, right? But obvious doesn't cut it when we're doing logic!
data Or (A B : Set) : Set where
 left : A -> Or A B
 right : B -> Or A B

or-case-helper : (p q : Bool) -> p ∨ q ≡ True -> Or (p ≡ True) (q ≡ True)
or-case-helper True True pf = left refl
or-case-helper True False pf = left refl
or-case-helper False True pf = right refl


-- Now what we can do is show that if something is *provable* then the meaning of it is always true!
-- This proof is *complicated* but it's important because it means that if we can prove something
-- that's because it's true
-- This again has some analogies to compiler writing! This is kind of like a typechecking theorem that would say
-- "If a program is well typed, it compiles and behaves correctly"
-- No, really, that's a thing you might have to prove one day!
-- If you filled in all the bits above correctly then this will go *just great*
-- Uncomment this block to see the magic happen

{-
soundness : {f : Formula} -> Provable f -> eval f ≡ True
soundness true-is-true = refl
soundness (∧f-intro f1 f2 p1 p2) = proof-helper
  where
    proof-helper : eval (f1 ∧f f2) ≡ True
    proof-helper with eval f1 | eval f2 | soundness p1 | soundness p2
    ... | b1 | b2 | refl | refl = refl
soundness (spec-l f1 f2 p) = eval-and-helper-1 f1 f2 (soundness p) -- look at which theorem above will help you here!
soundness (spec-r f1 f2 p) = eval-and-helper-2 f1 f2 (soundness p)
soundness (gen-l f1 f2 p) rewrite (soundness p) = orTrue-l (eval f2)
soundness (gen-r f1 f2 p) rewrite (soundness p) = orTrue-r (eval f1)
soundness (modus-pony f1 f2 p1 p2) = eval-mp-helper' (eval f1) (eval f2) (soundness p2) (soundness p1)
soundness (∨f-by-cases f1 f2 f3 p pl pr) = proof-helper
 where
   proof-helper : eval f3 ≡ True
   proof-helper with or-case-helper (eval f1) (eval f2) (soundness p)
   ... | left x = eval-mp-helper' _ _ x (soundness pl)
   ... | right x = eval-mp-helper' _ _ x (soundness pr)

soundness (double-neg f p) = doubleNeg-helper (eval f) (soundness p)
soundness (modus-tolly f1 f2 p q) = eval-mp-helper' _ _ (soundness q) (soundness p)
-}
