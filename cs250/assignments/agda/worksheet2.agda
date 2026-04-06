module worksheet2 where

{-

Reminder: to type symbols

 ≡ is \ = =

 ∧ is \ and

 ∨ is \ or

 ¬ is \ neg

-}

-- we again use the identity relation that we used in the first worksheet
data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a

infixl 1 _≡_

-- Booleans are a nice simple type, a bool is either True or it is False
data Bool : Set where
 True : Bool
 False : Bool

-- now we can define things like ∧ and ∨ by cases over their variables, which is basically just a truth table!!
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

-- Exercise: fill this in by casing over p and q
_|->_ : Bool -> Bool -> Bool
True  |-> True = True
True  |-> False = False
False |-> b = True

infixr 2 _|->_


-- we can state our allowed rules of inference using the implication operator |->, for example the following formulae
-- are ways of encoding modus ponens and the double negation rule

-- Exercise: Follow these steps
-- 1. case over p
-- 2. case over q
-- 3. once all you have are various combos of true and false then type refl in each of the holes and refine with C-c C-r
-- this is the agda version of a truth table!
-- each line is checking that the "column" that describes modus ponens is True no matter what values p and q take
mp : (p q : Bool) -> ((p |-> q) ∧ p) |-> q ≡ True
mp p q = {!!}

-- Exercise: do the same thing to prove double negation is valid
double-neg : (p : Bool) -> (¬ (¬ p)) |-> p ≡ True
double-neg p = {!!}

{-
If we have to write all of these cases by hand it's going to get boring, instead we can take advantage of the
fact that this is a programming language to automate things for us.

Here we present isTautology functions for formulas with
 * one variable
 * two variables
 * three variables

you could do more but we won't need it for the purposes of this class

If you look at these functions, what do you think they do?

What's happening is that it's checking to make sure that the formula is *always* true, which it can do exhaustively by trying all the possible cases and ∧-ing all the clauses together
-}

isTautology₁ : (Bool -> Bool) -> Bool
isTautology₁ f = (f True) ∧ (f False)

-- Check if a 2-variable formula (Bool → Bool → Bool) is a tautology
isTautology₂ : (Bool -> Bool -> Bool) -> Bool
isTautology₂ f = (f True True) ∧ (f True False) ∧ (f False True) ∧ (f False False)

-- Check if a 3-variable formula is a tautology
isTautology₃ : (Bool -> Bool -> Bool -> Bool) -> Bool
isTautology₃ f = (f True True True) ∧ (f True True False)
               ∧ (f True False True)  ∧ (f True False False)
               ∧ (f False True True)  ∧ (f False True False)
               ∧ (f False False True) ∧ (f False False False)


modus-ponens : Bool -> Bool -> Bool
modus-ponens p q = ((p |-> q) ∧ p) |-> q

-- now we can check modus ponens like this
check-modus-ponens :  isTautology₂ modus-ponens ≡ True
check-modus-ponens = refl

-- We can do other useful rules too

∧-elim-1 : Bool -> Bool -> Bool
∧-elim-1 p q = p ∧ q |-> q

check-∧-elim-1 : isTautology₂ ∧-elim-1 ≡ True
check-∧-elim-1 = refl

-- we can even do one of the really nasty rules like ∨-elimination
∨-elim : Bool -> Bool -> Bool -> Bool
∨-elim p q r = (p ∨ q) ∧ (p |-> r) ∧ (q |-> r) |-> r

check-∨-elim : isTautology₃ ∨-elim ≡ True
check-∨-elim = refl
-- This is the most powerful `refl` in existence, it just computed a bunch of a cases and `and`ed them together!

-- but first bi-implication
bi-imp : Bool -> Bool -> Bool
bi-imp p q = (p |-> q) ∧ (q |-> p)

-- or de morgan's laws
deMorg1 : Bool -> Bool -> Bool
deMorg1 p q = bi-imp (¬ (p ∨ q)) (¬ p ∧ ¬ q)

deMorg1-check : isTautology₂ deMorg1 ≡ True
deMorg1-check = refl -- it's as shrimple as that

-- Exercise: finish the definition of xor, this is a lot like when you wrote your definitions of + &c. in worksheet 1
xor : Bool -> Bool -> Bool
xor p q = {!!}

-- Exercise: prove the following theorem by cases on p and q and filling in refl
xor-id : (p q : Bool) -> xor p (xor p q) ≡ q
xor-id p q = {!!}

-- now fill in the definition for nand (not and)
-- either via cases or by just writing definition in terms of ¬ and ∧
nand : Bool -> Bool -> Bool
nand p q = {!!}

-- Exercise: write a version of implication by just filling in the hole with a combination of nand, p, q
-- yes this is just your other homework too!
nand-imp : Bool -> Bool -> Bool
nand-imp p q = {!!}

-- and you should be able to do cases over p and q and then fill in refl in the holes and have this pass
nand-imp-check : (p q : Bool) -> nand-imp p q ≡ p |-> q
nand-imp-check p q = {!!}
