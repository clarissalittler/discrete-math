module worksheet4 where

-- we define the natural numbers yet again
data Nat : Set where
 zero : Nat
 succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + n2 = n2
succ n1 + n2 = succ (n1 + n2)


-- and here we redefine the notion of equality
data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a

infixl 1 _≡_
-- this next line is going to let us use a fun trick called "rewrite" later in the file
{-# BUILTIN EQUALITY _≡_ #-}

-- we also need a few important facts about what ≡ means

-- first, we need a thing that says if you feed equal things into functions you get equal results
cong1 : {A B : Set} {a1 a2 : A} -> (f : A -> B) -> a1 ≡ a2 -> f a1 ≡ f a2
cong1 f refl = refl

-- here's a trivial use of cong1 to give you a concrete idea of what it does
-- we're using it along with the "partial application of treating (n1 + ) as its own function that takes
-- one more argument in order to show that if n2 = n3 then we can add n1 to the left on both sides and maintain
-- equality
-- makes sense, right?
-- Again for practice write out the meaning of this type in words
-- for all ...??
silly-theorem : (n1 n2 n3 : Nat) -> n2 ≡ n3 -> n1 + n2 ≡ n1 + n3
silly-theorem n1 n2 n3 p = cong1 (n1 +_) p


-- next, that it's *symmetric*, which means that if a = b then b = a
-- this proof is as trivial as the others
symm : {A : Set} {a b : A} -> a ≡ b -> b ≡ a
symm refl = refl

-- we *also* need that ≡ is transitive
trans : {A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
trans refl refl = refl

infixl 6 _+_

-- so this is a theorem that goes through automatically because this is how we defined the computation
zero-plus : {n : Nat} -> zero + n ≡ n
zero-plus = refl

-- Cool well + is commutative so obviously it should be just as easy the other way...right?
-- Oh no! Why doesn't this work?
-- plus-zero : {n : Nat} -> n + zero ≡ n
-- plus-zero {n} = {!refl!}

-- Agda doesn't know that + is commutative, we have to show that
-- The good news is that it follows from the definition it just takes a little bit of work
-- and this file will be all about building up through showing that this is true
-- Our first theorem is a bit of a warmup and I'm going to do it for you and explain it
-- This is what it's going to look like in the end, but I want you to follow the instructions below to do it yourself
-- along with me
{- 
plus-zero : (n : Nat) -> n + zero ≡ n
plus-zero zero = refl -- this zero case is trivial because 0 + 0 = 0 by the first rule of _+_
plus-zero (succ n) = cong1 succ (plus-zero n)
-}

plus-zero : (n : Nat) -> n + zero ≡ n
plus-zero zero = refl
plus-zero (succ n) = {!!}
-- this one is tricky so we'll talk about it in some detail and I want you to follow long with my descriptions
-- First, note that the type of this hole is (succ n + zero) ≡ succ n
-- that's our goal
-- well what's the inductive hypothesis? type plus_zero n into the hole and type C-c C-d
-- now you can see that the inductive hypothesis gives you something of the form (n + zero ≡ n)
-- so the *really* what we need is to take the IH and show that if you apply succ to both sides it's still true
-- well that's exactly what our cong1 function gives you!
-- so first type cong1 in the hole and refine C-c C-r
-- look at that, it made new holes for you!
-- In the first hole, type succ and refine again
-- nowww look at the type of the remaining hole
-- isn't that just your inductive hypothesis?
-- so type (plus-zero n) in the hole and refine and then you're done!


-- and this kind of thing is *such* a common pattern in Agda that there's even a command, rewrite, that
-- lets us just use the inductive hypothesis to "rewrite" the goal. Look at the hole there and what the goal actually is!
-- Look at how both sides are just succ n now, which means you can use your good friend refl to clear this goal
-- it's a lot nicer, right?
plus-zero' : {n : Nat} -> n + zero ≡ n
plus-zero' {zero} = refl
plus-zero' {succ n} rewrite (plus-zero' {n}) = {!!}

-- now prove the following theorem, which is that addition is associative, in essentially the same way, by yourself
-- make sure to start by setting up the *first* argument as the variable you're doing induction over, just like with plus-zero

plus-assoc : (n1 n2 n3 : Nat) -> n1 + n2 + n3 ≡ n1 + (n2 + n3)
plus-assoc n1 n2 n3 = {!!}

-- okay now we need to actually prove our next little theorem to get us towards commutativity
-- you can do this either with rewrite *or* with cong1
-- I've set up the induction for you because there are *two* variables here but you want to do induction on the
-- first one because that's the leftmost argument of +, i.e. the one our recursive definition was based on
plus-succ : (n n' : Nat) -> n + succ n' ≡ succ (n + n')
plus-succ n n' = {!!}

-- okay now we're able to prove that addition is commutative
-- but it's going to take a bit of work so I'm going to walk you through it
-- the first goal is *almost* plus zero, but the sides of the equation are reversed
-- is there something that will let you swap a ≡ b and b ≡ a ?
-- finally, for the last one you're actually going to need to use the transitivity theorem we proved earlier
-- so start by typing trans and hitting refine
-- think about what you need here:
-- you need to first prove that
-- succ (n + n') = succ (n' + n)
-- which is cong1 applied to the inductive hypothesis
-- then the second part of the trans is reversing (plus-succ n' n) to
-- to turn it into the right connecting thing
plus-comm : (n n' : Nat) -> n + n' ≡ n' + n
plus-comm zero n' = {!!}
plus-comm (succ n) n' = {!!}

-- that's all for this time!
-- Next time we're going to jump into some more advanced proving with lists and other datatypes
