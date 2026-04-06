module worksheet5 where

data _≡_ {A : Set} : A -> A -> Set where
 refl : {a : A} -> a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}
infixl 1 _≡_

data Nat : Set where
 zero : Nat
 succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + n = n
(succ n) + n' = succ (n + n')

infixl 6 _+_

one = succ zero
two = succ (succ zero)
three = succ (succ (succ zero))
four = succ three

cong1 : {A B : Set} {a1 a2 : A} -> (f : A -> B) -> a1 ≡ a2 -> f a1 ≡ f a2
cong1 f refl = refl


-- are you sick of induction on the naturals? I sure am!
-- maybe we should try some more interesting things now, huh??

-- did you know you can make all sorts of other types?
-- Here's a list!

data List (A : Set) : Set where
 nil : List A
 cons : A -> List A -> List A

-- you should be familiar with this kind of linked list!
-- it looks less intimidating without the pointers, eh?

-- let's define a length function as a warmup
-- go ahead and try this by induction on the argument l
-- and do the sensible thing
-- nil has a length of 0
-- cons is succ of the length of the rest of the list 
length : {A : Set} -> List A -> Nat
length nil = zero
length (cons x l) = succ (length l)

-- Okay now what about a pop function? You did the last one so I'll take this one
pop : {A : Set} -> List A -> A
pop (cons x l) = x
pop nil = {!!} -- huh, uhh what goes in here? This seems like a problem!

-- so programming languages like Agda don't let you just not cover cases
-- you *must* put something in there for the program to be complete
-- now there are some ways we could handle this, like defining a notion of <

data _<_ : Nat -> Nat -> Set where
 s< : {n1 n2 : Nat} -> n1 < n2 -> succ n1 < succ n2
 z< : {n1 : Nat} -> zero < succ n1

-- Can you read this and try to describe what this means? Why does it have two 
-- Your answer:

-- let's test that this might actually help us define our safe pop

safe-pop : {A : Set} -> (l : List A) -> zero < (length l) -> A
safe-pop l p = {!!} -- try doing cases on the variable l and see what happens

-- oh would you look at that, if we stipulate that the length is greater than zero then the nil case is rendered
-- impossible: we saw this happen as well in the last worksheet before this!

-- we can also define other useful functions like the ability to append
-- try doing this but first stare at the definition of + above and see if you can spot the similarity
-- in what you need to do
_++_ : {A : Set} -> List A -> List A -> List A
l1 ++ l2 = {!!}

-- okay so what we'd *like* is to prove that
-- length (l1 ++ l2) = length l1 + length l2
-- this is what mathematicians call a "commuting diagram" because it means there are two ways to get to the same
-- result. In this case, you can append then take the length or you can take the lengths and then add and these should be "the same" computation
-- this is *a lot* like proofs you did last time like plus-assoc, and as a hint you'll need to either use cong1 or rewrite like last time

+-and-++ : {A : Set} -> (l1 l2 : List A) -> length (l1 ++ l2) ≡ (length l1) + (length l2)
+-and-++ l1 l2 = {!!}

-- Now hold up, let's take a bit of a step back: we are writing functions *and proofs about those functions* in the same programming language
-- That's kind weird, right?
-- Well this is the world of high-assurance computing: you prove properties about your code in order to ensure some kinds of bugs aren't allowed to happen
-- Real proofs about real code is far more complicated than this, though!
-- Let's try and do something at least kinda interesting now, we can make binary search trees on natural numbers
-- If you need a refresher, a binary search tree is like a list except that rather than a next node it has a left and right node
data BTree : Set where
 branch : Nat -> BTree -> BTree -> BTree
 leaf : BTree

-- what makes this a search tree is that you insert into it in a particular ordered way
-- the left branch is always less-than-or-equal to the node which itself is always less than everything in the right branch
-- we're going to have to do some wild tricks, though, to make all of this work

-- we need to define a new relation that describes the possible relations between two numbers
-- n < n'
-- n > n' i.e. n' < n
-- n ≡ n'
data Ordering : Nat -> Nat -> Set where
 lt : {n n' : Nat} -> n < n' -> Ordering n n'
 gt : {n n' : Nat} -> n' < n -> Ordering n n'
 eq : {n n' : Nat} -> n ≡ n' -> Ordering n n'

-- and we can define a function that, given two numbers, returns an Ordering between them
-- there's a fun trick here where we do cases on the inductive hypothesis using this thing called `with`
--  you'll see an example of with below that you'll need to use
totalOrder : (n n' : Nat) -> Ordering n n'
totalOrder zero zero = eq refl
totalOrder zero (succ n') = lt z<
totalOrder (succ n) zero = gt z<
totalOrder (succ n) (succ n') with totalOrder n n'
... | lt x = lt (s< x)
... | gt x = gt (s< x)
... | eq refl = eq refl

-- now we can define our insert function and we're going to use `with` here again
-- you can type o in the hole and C-c C-c on it in order to break it down into cases
-- and handle the insert from there!
-- The only tricky bit is what to do if n and x are equal:
-- does your tree allow duplicates or not?
-- if it doesn't, then nothing about the tree changes
-- if it does, then you have to make a new branch that 
insert : Nat -> BTree -> BTree
insert n (branch x bl br) with totalOrder n x
... | o = {!!} 
insert n leaf = branch n leaf leaf

-- now here's the last bit!
-- let's write a function that converts this to a list in proper order
-- you can do this!!
toList : BTree -> List Nat
toList b = {!!}

-- proving that this is correct is a little *too* involved even for me to show you
-- but we can do a test for a really concrete set of numbers

finality : toList (insert one (insert four (insert two (insert zero (insert three leaf))))) ≡ (cons zero (cons one (cons two (cons three (cons four nil)))))
finality = {!!} -- if you write your definition correctly you should be able to type refl here and refine and you're done!
