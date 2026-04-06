-- Agda Worksheet 1: Introduction, Naturals, Integers, and Equality

-- This line declares the name of our Agda module.
-- All Agda code lives inside modules.
module worksheet1 where

{-
## BEFORE YOU GET STARTED!!!
* You type ≡ by hitting \ then = then = again
* IF YOU'RE ON AGDAPAD open a new file with the file menu first then call it worksheet1.agda
* Load the file with C-c and C-l (Ctrl + c then Ctrl + l) before you do anything else, all the other commands only work once the file is loaded and Agda is "on"
* IF YOU'RE ON AGDAPAD "turn in" your work by giving me the link to your session (just copy the URL) so I can look at it
* Also, seriously, agdapad is just a stopgap you should get a local install going with one of the methods discussed in class and linked in the pinned announcement


## Mini Agda Tutorial for Beginners

Welcome to Agda!

**What is Agda?**

*   Agda is a **functional programming language** similar in style to Haskell.
*   It's also a **proof assistant**. This means you can not only write programs but also write mathematical proofs about your programs and have Agda check their correctness.
*   The core feature enabling this is **dependent types**. This means types can depend on *values* (or "terms"). For example, the type of "a list of length `n`" depends on the *value* `n`.

**Why Learn Agda?**

*   To write programs with an extremely high degree of confidence in their correctness.
*   To explore the connections between programming and mathematical logic (the Curry-Howard correspondence).
*   To precisely express complex properties of data structures and functions.

**Editor Interaction (Common Commands)**

Agda is typically used within an editor like Emacs (with `agda-mode`) or Visual Studio Code (with the `agda-mode` extension). Here are the most essential commands (keys are often Emacs-based, VS Code usually maps them similarly or provides alternatives):

0. **Keyboard shorcuts**:
 Anything listed with a C-blah is given by hitting the Ctrl key and then whatever comes next. So C-c C-l really means "Ctrl-c at the same time, let go of Ctrl and c then hit Ctrl and l *or* hold Ctrl- and hit c then let go of c and hit l.
1.  **Load/Type-Check the File (`C-c C-l`)**: This is the most fundamental command. It loads the current file into Agda, checks it for errors (type errors, syntax errors), and highlights checked code. If there are errors, Agda will point them out. `C-c` means press `Ctrl` and `c` together.
2.  **Holes (`{!!}` or `?`)**: These are placeholders for code you haven't written yet. Agda treats them specially.
3.  **Goal Type and Context (`C-c C-,` or `C-c C-?` in a hole)**: When your cursor is inside a hole `{!!}`, this command tells you what type Agda expects you to provide there (`Goal`) and what variables and their types are available (`Context`). This is crucial for figuring out what to write.
4.  **Refine/Fill Hole (`C-c C-r` or `C-c C-SPACE` in a hole)**: If Agda can guess a part of the solution (like a function name or constructor based on the goal type), this command might partially fill the hole. `C-c C-SPACE` often tries to insert a constructor or function based on the expected type. You can also just start typing in the hole.
5.  **Case Split (`C-c C-c` on a variable in a hole, or `C-c C-CASE`)**: If you have a variable `x` in scope (visible via `C-c C-,`) and its type is a data type (like `Nat` or `Bool`), you can ask Agda to automatically create the different pattern-matching cases for `x`. Place the variable name `x` inside the hole (`{![x]!}` or just `{![ ]!}` and type `x`), then press `C-c C-c`. Agda will replace the line with clauses for each constructor (`zero`, `succ n` for `Nat`).
6.  **Check Type (`C-c C-d` or `C-c C-.` on a name)**: Place the cursor on an identifier (like `Nat`, `_+_`, `refl`) and press this command to see its type.
7.  **Go to Definition**: Standard editor navigation (like `M-.` in Emacs or `F12` in VS Code) often works to jump to where something is defined.
8.  **Comments**: Lines starting with `--` are single-line comments. Blocks can be commented using `{- ... -}`.

**Basic Syntax Seen Here:**

*   `module ... where`: Defines a namespace for your code.
*   `data ... : Set where`: Defines a new data type. `Set` is the type of "ordinary" types (like types in Haskell or Java).
*   `:`: Separates a name from its type (e.g., `zero : Nat`).
*   `=`: Defines a function or value.
*   `->`: Function type arrow (e.g., `Nat -> Nat` is a function from `Nat` to `Nat`).
*   `{A : Set}`: Introduces an implicit argument. Agda often infers these.
*   `_` (Underscores): Used in function/operator names (like `_+_`) to indicate where arguments go, making them infix or mixfix.
*   `infixl`, `infixr`, `infix`: Set operator precedence and associativity.

Now, let's look at the worksheet code with comments and hints. Remember to use `C-c C-l` to load the file and the other commands to interact with the holes!
-}

-- Definition of Propositional Equality (_≡_)

-- This defines a built-in type representing equality between two terms of the same type.
-- It's a "dependent" type because the resulting type (Set) depends on the *values* a and b.
-- For any type A, and any two values a and b of type A, (a ≡ b) is the *type* of proofs that a is equal to b.
data _≡_ {A : Set} : A -> A -> Set where
  -- The only way to construct a proof of equality is 'refl' (short for reflexivity).
  -- 'refl' states that any term 'a' is equal to itself.
  -- {a : A} means 'a' is an implicit argument; Agda can usually figure it out.
  -- Crucially, Agda only allows 'refl' if the two sides *compute* to the exact same thing.
  refl : {a : A} -> a ≡ a

-- This sets the equality operator to be left-associative with precedence level 1 (low).
infixl 1 _≡_

-- Definition of Natural Numbers (Nat)

-- We define natural numbers (0, 1, 2, ...) using Peano axioms.
data Nat : Set where
  -- The base case: 'zero' is a natural number.
  zero : Nat
  -- The inductive step: if 'n' is a natural number, then 'succ n' (successor of n) is also a natural number.
  succ : Nat -> Nat

-- Some convenient definitions for small natural numbers.
one : Nat
one = succ zero -- one is the successor of zero

two : Nat
two = succ one -- two is the successor of one

three : Nat
three = succ two -- three is the successor of two

four : Nat
four = succ three -- four is the successor of three

-- Definition of Addition (_+_)

-- This defines addition for natural numbers.
-- It works by *recursion* on the *left* argument (the one before the '+').
_+_ : Nat -> Nat -> Nat
-- Base case: If the left argument is 'zero', the sum is just the right argument 'n2'.
zero + n2 = n2
-- Recursive step: If the left argument is 'succ n1', the sum is the successor of ('n1' + 'n2').
-- We reduce the problem (succ n1 + n2) to a smaller one (n1 + n2).
succ n1 + n2 = succ (n1 + n2)

-- Sets addition to be left-associative with high precedence (10).
infixl 10 _+_

-- Definition of Subtraction (_-_)

-- Defining subtraction on natural numbers is a bit tricky because the result must also be a natural number (no negatives).
-- Convention: n - m is 0 if n <= m.
_-_ : Nat -> Nat -> Nat
-- Base case 1: Subtracting anything from zero results in zero.
zero - n2 = zero
-- Base case 2: Subtracting zero from a successor leaves the successor unchanged.
succ n1 - zero = succ n1
-- Recursive step: Subtracting (succ n2) from (succ n1) is the same as subtracting n2 from n1.
-- This rule effectively "cancels" one 'succ' from both sides.
succ n1 - succ n2 = n1 - n2

-- Sets subtraction to be left-associative with medium precedence (5).
infixl 5 _-_

-- Example Proofs/Tests using Equality

-- This defines a proof that (two - two) is equal to zero.
-- Agda computes 'two - two' step-by-step:
-- two - two = (succ one) - (succ one) -> one - one by the third rule of subtraction
--           = (succ zero) - (succ zero) -> zero - zero by the third rule again
--           = zero by the first rule of subtraction
-- Since the left side computes to 'zero', it's equal to the right side 'zero'.
-- So, 'refl' is a valid proof.
baby-proof1 : two - two ≡ zero
baby-proof1 = refl

-- This defines a proof that (one + one) is equal to two.
-- Agda computes 'one + one':
-- one + one = (succ zero) + one -> succ (zero + one) by the second rule of addition
--           = succ (one) by the first rule of addition
--           = two by the definition of 'two'
-- Since the left side computes to 'two', it's equal to the right side 'two'.
-- 'refl' is a valid proof.
baby-proof2 : one + one ≡ two
baby-proof2 = refl

-- Exercise 1: Multiplication (_*_)

-- Hint: Define multiplication by recursion on the first argument 'n1', similar to how addition was defined.
-- Think about the base case: What is `zero * n2`? It should be `zero`.
-- Think about the recursive step: What is `(succ n1) * n2`? It's `n2` added to the result of `n1 * n2`.
-- You'll need to use the addition operator `_+_` you defined earlier.
-- Steps:
-- 1. Put your cursor in the hole `{!!}`.
-- 2. Type `n1` inside the hole: `{![n1]!}`.
-- 3. Press `C-c C-c` (or `C-c C-CASE`) to perform case splitting on `n1`.
-- 4. Agda will generate two lines, one for the `zero` case and one for the `succ n1'` case.
-- 5. Fill in the right-hand side for each case based on the hints above.
_*_ : Nat -> Nat -> Nat
n1 * n2 = {!!}

-- Sets multiplication to be left-associative with precedence 6
infixl 6 _*_


-- uncomment and reload the file (C-c C-l) to check the tests work once you've defined _*_.
-- If they don't load, your definition is likely incorrect or incomplete.
-- mult-test-1 : one * two ≡ two
-- mult-test-1 = refl

-- mult-test-2 : zero * four ≡ zero
-- mult-test-2 = refl

-- mult-test-3 : two * two ≡ four
-- mult-test-3 = refl


-- Exercise 2: Exponentiation (_**_)

-- Hint: Define exponentiation (n1 raised to the power of n2) by recursion on the *second* argument 'n2'.
-- Think about the base case: What is `n1 ** zero`? It should be `one`. Remember `one` is `succ zero`.
-- Think about the recursive step: What is `n1 ** (succ n2)`? It's `n1` multiplied by the result of `n1 ** n2`.
-- You'll need to use the multiplication operator `_*_` you just defined.
-- Steps:
-- 1. Put your cursor in the hole `{!!}`.
-- 2. Type `n2` inside the hole: `{![n2]!}`.
-- 3. Press `C-c C-c` (or `C-c C-CASE`) to perform case splitting on `n2`.
-- 4. Agda will generate two lines, one for the `zero` case and one for the `succ n2'` case.
-- 5. Fill in the right-hand side for each case based on the hints above.
_**_ : Nat -> Nat -> Nat
n1 ** n2 = {!!}

-- Sets exponentiation to be left-associative with precedence 3 (lower than multiplication).
infixl 3 _**_

-- uncomment to make sure these tests pass once you've defined _**_.
-- exp-test-1 : four ** zero ≡ one
-- exp-test-1 = refl

-- Exploring Integer Representations

-- How would we represent integers (positive, negative, and zero)?
-- Here are two possibilities:

-- Representation 1: Using Successor and Predecessor relative to Zero
-- This represents integers like ..., -2, -1, 0, 1, 2, ...
-- as ..., pred (pred zero), pred zero, zero, succ zero, succ (succ zero), ...
data Int1 : Set where
 pred : Int1 -> Int1  -- Represents "subtract one"
 succ : Int1 -> Int1  -- Represents "add one"
 zero : Int1          -- Represents the number zero

-- Representation 2: Using a Sign and a Natural Number Magnitude
-- This uses a tag (`pos` or `neg`) and a natural number.
data Int2 : Set where
 pos : Nat -> Int2  -- Represents a non-negative integer (+n)
 neg : Nat -> Int2  -- Represents a non-positive integer (-n)
                    -- Note: zero can be represented as pos zero or neg zero!

-- Exercise 3: Addition for Int1

-- Hint: This is more complex than Nat addition because you have `pred` and `succ`.
-- You need to define `plus-int1` by pattern matching on *both* arguments.
-- Steps:
-- 1. Put your cursor in the hole `{!!}`.
-- 2. Type `i1` inside the hole: `{![i1]!}`. Press `C-c C-c`. This splits on `i1`.
-- 3. You'll get cases for `zero`, `succ i1'`, `pred i1'`.
-- 4. Inside *each* of these cases, you now need to split on `i2`. For example, in the line for `plus-int1 zero i2 = {!!}`, put `i2` in the hole `{![i2]!}` and press `C-c C-c`.
-- 5. This will give you many cases (zero+zero, zero+succ, zero+pred, succ+zero, succ+succ, succ+pred, pred+zero, pred+succ, pred+pred).
-- 6. Think about how `succ` and `pred` interact. For example:
--    - `zero + y` should just be `y`.
--    - `x + zero` should just be `x`.
--    - `succ x + y` could recursively call `plus-int1` as `succ (plus-int1 x y)`.
--    - `pred x + y` could recursively call `plus-int1` as `pred (plus-int1 x y)`.
--    - What happens specifically with `succ x + pred y` or `pred x + succ y`? They should cancel out, resulting in `plus-int1 x y`.
-- Fill in the right-hand side for all 9 generated cases.
plus-int1 : Int1 -> Int1 -> Int1
plus-int1 i1 i2 = {!!}

-- Exercise 4: Addition for Int2

-- Hint: This requires pattern matching on both arguments (`i1` and `i2`) to see if they are `pos` or `neg`.

plus-int2 : Int2 -> Int2 -> Int2
plus-int2 i1 i2 = {!!}


-- Integer Addition Tests (Uncomment to Check)

-- This test checks if `pred zero` (-1) plus `succ zero` (+1) equals `zero` (0) for Int1.
-- This should pass if your `plus-int1` definition correctly handles cancellation.
-- Use C-c C-l to reload and check.
-- plus-int1-test : plus-int1 (pred zero) (succ zero) ≡ zero
-- plus-int1-test = refl

-- These tests check `pos two` (+2) plus `neg two` (-2) for Int2.
-- Depending on how you defined the `pos n + neg m` case (specifically when n = m),
-- the result might compute to `pos zero` or `neg zero`.
-- Only *one* of these tests will pass with `refl`, demonstrating an ambiguity in the Int2 representation of zero.
-- Uncomment *one* and see if it passes after defining `plus-int2` (using C-c C-l). If not, try the other.

-- plus-int2-test : plus-int2 (pos two) (neg two) ≡ (pos zero)
-- plus-int2-test = refl

-- plus-int2-test' : plus-int2 (pos two) (neg two) ≡ (neg zero)
-- plus-int2-test' = refl


-- The Problem of Equality

-- You'll notice other weird things about these integer representations though.
-- The following "theorems" feel like they *should* be true, but Agda's `≡` won't accept `refl`.

-- Why doesn't this work? Because `pos zero` and `neg zero` are built using different constructors (`pos` vs `neg`).
-- Agda's `≡` only works if two things compute to the *exact same form*. They represent the same *idea* (zero), but structurally they are different.
-- There's nothing you can fill in the hole `{!!}` to make this type-check using just `refl`. You would need a more sophisticated proof.
fail-1 : pos zero ≡ neg zero
fail-1 = {!!} -- Cannot be proved with 'refl'

-- Why doesn't this work?
-- `pred (succ zero)` computes to itself. It doesn't simplify further based on the definitions we have.
-- `succ (pred zero)` computes to itself. It doesn't simplify further.
-- Even though applying "subtract one" then "add one" *should* be the same as applying "add one" then "subtract one" (both should ideally simplify to the identity),
-- Agda only performs computations based on the *definitions* given. It doesn't automatically know `pred (succ x) = x`.
-- Agda sees `pred (succ zero)` and `succ (pred zero)` as distinct, non-equal terms based *only* on computation rules.
fail-2 : pred (succ zero) ≡ succ (pred zero)
fail-2 = {!!} -- Cannot be proved with 'refl'


-- The reason these fail relates to the difference between *intensional* and *extensional* equality.
-- Agda's built-in `_≡_` is *intensional*: it cares about *how* things are defined and computed. Two things are equal only if they compute to the very same expression (syntactically, after normalization).
-- *Extensional* equality means two things are equal if they behave the same way or represent the same abstract value (e.g., `pos zero` and `neg zero` both represent the abstract integer 0). We often *want* `pos zero` and `neg zero` to be equal in this extensional sense, but Agda's `≡` doesn't capture that directly without more advanced techniques (like defining custom equality relations called "Setoids" or using "Quotient Types", which are beyond this worksheet).
-- This is a fundamental concept in type theory! For now, just be aware that `a ≡ b` in Agda means `a` and `b` compute to the *exact same* term.

