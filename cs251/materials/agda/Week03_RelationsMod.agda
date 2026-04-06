{-# OPTIONS --type-in-type #-}

module Week03_RelationsMod where

open import Common

-- Binary relations
Rel : Set -> Set
Rel A = A -> A -> Set

-- Heterogeneous relations
HRel : Set -> Set -> Set
HRel A B = A -> B -> Set

-- Relation properties
Reflexive : {A : Set} -> Rel A -> Set
Reflexive {A} R = (x : A) -> R x x

Symmetric : {A : Set} -> Rel A -> Set
Symmetric {A} R = (x y : A) -> R x y -> R y x

Transitive : {A : Set} -> Rel A -> Set
Transitive {A} R = (x y z : A) -> R x y -> R y z -> R x z

Antisymmetric : {A : Set} -> Rel A -> Set
Antisymmetric {A} R = (x y : A) -> R x y -> R y x -> Eq x y

Total : {A : Set} -> Rel A -> Set
Total {A} R = (x y : A) -> Sum (R x y) (R y x)

Irreflexive : {A : Set} -> Rel A -> Set
Irreflexive {A} R = (x : A) -> Not (R x x)

-- Equivalence relations
Equivalence : {A : Set} -> Rel A -> Set
Equivalence R = Pair (Reflexive R) (Pair (Symmetric R) (Transitive R))

-- Preorder (reflexive and transitive)
Preorder : {A : Set} -> Rel A -> Set
Preorder R = Pair (Reflexive R) (Transitive R)

-- Partial order (preorder + antisymmetric)
PartialOrder : {A : Set} -> Rel A -> Set
PartialOrder R = Pair (Preorder R) (Antisymmetric R)

-- Total order (partial order + total)
TotalOrder : {A : Set} -> Rel A -> Set
TotalOrder R = Pair (PartialOrder R) (Total R)

-- Strict order (irreflexive and transitive)
StrictOrder : {A : Set} -> Rel A -> Set
StrictOrder R = Pair (Irreflexive R) (Transitive R)

-- Propositional equality is an equivalence relation
eqRefl : {A : Set} -> Reflexive (Eq {A})
eqRefl x = refl

eqSym : {A : Set} -> Symmetric (Eq {A})
eqSym x y p = sym p

eqTrans : {A : Set} -> Transitive (Eq {A})
eqTrans x y z p q = trans p q

eqEquivalence : {A : Set} -> Equivalence (Eq {A})
eqEquivalence = pair eqRefl (pair eqSym eqTrans)

-- Leq is a preorder
leqPreorder : Preorder Leq
leqPreorder = pair leqRefl (\x y z -> leqTrans)

-- Relation composition
_∘R_ : {A B C : Set} -> HRel B C -> HRel A B -> HRel A C
(R ∘R S) x z = Sigma _ (\y -> Pair (S x y) (R y z))

-- Inverse of a relation
Inverse : {A B : Set} -> HRel A B -> HRel B A
Inverse R y x = R x y

-- Reflexive closure
ReflClosure : {A : Set} -> Rel A -> Rel A
ReflClosure R x y = Sum (Eq x y) (R x y)

-- Symmetric closure
SymClosure : {A : Set} -> Rel A -> Rel A
SymClosure R x y = Sum (R x y) (R y x)

-- Reflexive closure is reflexive
reflClosureRefl : {A : Set} {R : Rel A} -> Reflexive (ReflClosure R)
reflClosureRefl x = inl refl

-- Symmetric closure is symmetric
symClosureSym : {A : Set} {R : Rel A} -> Symmetric (SymClosure R)
symClosureSym x y (inl rxy) = inr rxy
symClosureSym x y (inr ryx) = inl ryx

-- Equivalence classes
EquivClass : {A : Set} -> Rel A -> A -> Pred A
EquivClass R x y = R x y

-- Representatives: every element is in its own equivalence class (if R is reflexive)
classContainsSelf : {A : Set} {R : Rel A} -> Reflexive R ->
  (x : A) -> x ∈ EquivClass R x
classContainsSelf rRefl x = rRefl x

-- Equivalent elements have the same equivalence class (if R is an equivalence)
sameClassIfEquiv : {A : Set} {R : Rel A} -> Equivalence R ->
  (x y z : A) -> R x y -> (R x z -> R y z)
sameClassIfEquiv (pair _ (pair rsym rtrans)) x y z rxy rxz =
  rtrans y x z (rsym x y rxy) rxz

-- Quotient set (defined as predicates that are equivalence classes)
Quotient : {A : Set} -> Rel A -> Set
Quotient {A} R = Sigma A (\x -> Unit)

-- Modular arithmetic
CongruentMod : Nat -> Nat -> Nat -> Set
CongruentMod n a b = Sigma Nat (\k -> Eq (a + k * n) b)

-- Alternative definition using divisibility
Divides : Nat -> Nat -> Set
Divides d n = Sigma Nat (\k -> Eq (k * d) n)

-- Congruence is reflexive
congRefl : (n a : Nat) -> CongruentMod n a a
congRefl n a = sigma zero (addZeroRight a)

-- Modular arithmetic with symmetric definition
data ModEq (n : Nat) : Nat -> Nat -> Set where
  modEqDiff : {a b : Nat} -> (k : Nat) -> Eq (a + k * n) b -> ModEq n a b
  modEqDiffSym : {a b : Nat} -> (k : Nat) -> Eq (b + k * n) a -> ModEq n a b

-- ModEq is reflexive
modEqRefl : (n a : Nat) -> ModEq n a a
modEqRefl n a = modEqDiff zero (addZeroRight a)

-- ModEq is symmetric
modEqSym : {n a b : Nat} -> ModEq n a b -> ModEq n b a
modEqSym (modEqDiff k eq) = modEqDiffSym k eq
modEqSym (modEqDiffSym k eq) = modEqDiff k eq

-- Functional relation
Functional : {A B : Set} -> HRel A B -> Set
Functional {A} {B} R = (a : A) (b1 b2 : B) -> R a b1 -> R a b2 -> Eq b1 b2

-- Total relation (left-total)
LeftTotal : {A B : Set} -> HRel A B -> Set
LeftTotal {A} {B} R = (a : A) -> Sigma B (\b -> R a b)

-- A functional and left-total relation is essentially a function
relToFun : {A B : Set} {R : HRel A B} -> Functional R -> LeftTotal R -> A -> B
relToFun {R = R} func total a with total a
... | sigma b _ = b

-- Kernel of a function (induces an equivalence relation)
Kernel : {A B : Set} -> (A -> B) -> Rel A
Kernel f x y = Eq (f x) (f y)

-- Kernel is always an equivalence relation
kernelEquiv : {A B : Set} (f : A -> B) -> Equivalence (Kernel f)
kernelEquiv f = pair (\x -> refl) (pair (\x y -> sym) (\x y z -> trans))

-- ============================================
-- ADVANCED NUMBER THEORY
-- ============================================

open import Common using (_^_; mod; gcd; Coprime; _∣_; div)

-- Euler's totient function φ(n) = count of k ∈ [1,n] with gcd(k,n) = 1
-- We define it abstractly; computing it requires more machinery
postulate
  φ : Nat -> Nat

  -- φ(1) = 1
  φ-one : Eq (φ one) one

  -- φ(p) = p - 1 for prime p
  φ-prime : (p : Nat) -> Set -> Eq (φ p) (p - one)

  -- φ is multiplicative: φ(mn) = φ(m)φ(n) when gcd(m,n) = 1
  φ-multiplicative : (m n : Nat) -> Coprime m n -> Eq (φ (m * n)) (φ m * φ n)

-- ============================================
-- FERMAT'S LITTLE THEOREM
-- ============================================

{-
  Fermat's Little Theorem:
  If p is prime and gcd(a, p) = 1, then a^(p-1) ≡ 1 (mod p)

  In type theory, we state this as:
  For prime p and a coprime to p, (a ^ (p - 1)) mod p = 1
-}

-- Primality (simplified definition)
data Prime : Nat -> Set where
  prime : (p : Nat) ->
          Leq (succ (succ zero)) p ->  -- p ≥ 2
          ((d : Nat) -> d ∣ p -> Sum (Eq d one) (Eq d p)) ->  -- only divisors are 1 and p
          Prime p

-- Fermat's Little Theorem (stated as axiom - proof requires group theory)
postulate
  fermatLittle : (p : Nat) -> Prime p -> (a : Nat) -> Coprime a p ->
    Eq (mod (a ^ (p - one)) p) one

-- Corollary: a^p ≡ a (mod p) for any a
postulate
  fermatLittleAlt : (p : Nat) -> Prime p -> (a : Nat) ->
    Eq (mod (a ^ p) p) (mod a p)

-- ============================================
-- EULER'S THEOREM (generalization of Fermat)
-- ============================================

{-
  Euler's Theorem:
  If gcd(a, n) = 1, then a^φ(n) ≡ 1 (mod n)

  This generalizes Fermat's Little Theorem (when n = p prime, φ(p) = p - 1)
-}

postulate
  eulerTheorem : (n : Nat) -> Leq one n -> (a : Nat) -> Coprime a n ->
    Eq (mod (a ^ φ n) n) one

-- ============================================
-- CHINESE REMAINDER THEOREM
-- ============================================

{-
  Chinese Remainder Theorem:
  If gcd(n₁, n₂) = 1, then for any a₁, a₂, there exists unique x (mod n₁n₂) with:
    x ≡ a₁ (mod n₁)
    x ≡ a₂ (mod n₂)
-}

-- System of two congruences
record CRTSystem : Set where
  field
    n1 n2 : Nat
    a1 a2 : Nat
    coprime : Coprime n1 n2

-- CRT solution exists and is unique mod n1*n2
postulate
  crtSolution : (sys : CRTSystem) ->
    Sigma Nat (\x ->
      Pair (Eq (mod x (CRTSystem.n1 sys)) (mod (CRTSystem.a1 sys) (CRTSystem.n1 sys)))
           (Eq (mod x (CRTSystem.n2 sys)) (mod (CRTSystem.a2 sys) (CRTSystem.n2 sys))))

  crtUnique : (sys : CRTSystem) -> (x y : Nat) ->
    Eq (mod x (CRTSystem.n1 sys)) (mod (CRTSystem.a1 sys) (CRTSystem.n1 sys)) ->
    Eq (mod x (CRTSystem.n2 sys)) (mod (CRTSystem.a2 sys) (CRTSystem.n2 sys)) ->
    Eq (mod y (CRTSystem.n1 sys)) (mod (CRTSystem.a1 sys) (CRTSystem.n1 sys)) ->
    Eq (mod y (CRTSystem.n2 sys)) (mod (CRTSystem.a2 sys) (CRTSystem.n2 sys)) ->
    Eq (mod x (CRTSystem.n1 sys * CRTSystem.n2 sys))
       (mod y (CRTSystem.n1 sys * CRTSystem.n2 sys))

-- ============================================
-- MODULAR INVERSE
-- ============================================

-- Modular inverse: b such that a*b ≡ 1 (mod n)
HasModInverse : Nat -> Nat -> Set
HasModInverse a n = Sigma Nat (\b -> Eq (mod (a * b) n) one)

-- Modular inverse exists iff gcd(a, n) = 1
postulate
  modInverseExists : (a n : Nat) -> Leq one n -> Coprime a n -> HasModInverse a n
  modInverseOnlyIfCoprime : (a n : Nat) -> HasModInverse a n -> Coprime a n

-- ============================================
-- EXERCISES
-- ============================================

{-
  EXERCISE 1: Prove that divisibility is reflexive
  Every number divides itself: n | n
-}
exercise-divRefl : (n : Nat) -> n ∣ n
exercise-divRefl n = sigma one (mulOneLeft n)

{-
  EXERCISE 2: Prove that divisibility is transitive
  If a | b and b | c, then a | c
-}
postulate
  exercise-divTrans : (a b c : Nat) -> a ∣ b -> b ∣ c -> a ∣ c

{-
  EXERCISE 3: Prove that if d | a and d | b, then d | (a + b)
-}
postulate
  exercise-divSum : (d a b : Nat) -> d ∣ a -> d ∣ b -> d ∣ (a + b)

{-
  EXERCISE 4: Show that 1 divides everything
-}
exercise-oneDivides : (n : Nat) -> one ∣ n
exercise-oneDivides n = sigma n (trans (mulComm n one) (mulOneLeft n))

{-
  EXERCISE 5: Show that every number divides 0
-}
exercise-dividesZero : (n : Nat) -> n ∣ zero
exercise-dividesZero n = sigma zero refl
