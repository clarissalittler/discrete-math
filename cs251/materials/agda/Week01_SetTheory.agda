{-# OPTIONS --type-in-type #-}

module Week01_SetTheory where

open import Common

-- Basic set operations modeled as predicates
_⊆_ : {A : Set} -> Pred A -> Pred A -> Set
_⊆_ {A} P Q = (x : A) -> P x -> Q x

SetEq : {A : Set} -> Pred A -> Pred A -> Set
SetEq P Q = Pair (P ⊆ Q) (Q ⊆ P)

_∩_ : {A : Set} -> Pred A -> Pred A -> Pred A
(P ∩ Q) x = Pair (P x) (Q x)

_∪_ : {A : Set} -> Pred A -> Pred A -> Pred A
(P ∪ Q) x = Sum (P x) (Q x)

infix 4 _⊆_
infixr 6 _∩_
infixr 5 _∪_

Compl : {A : Set} -> Pred A -> Pred A
Compl P x = Not (P x)

-- Set difference
_∖_ : {A : Set} -> Pred A -> Pred A -> Pred A
(P ∖ Q) x = Pair (P x) (Not (Q x))

infixl 6 _∖_

-- Empty set and universal set
EmptySet : {A : Set} -> Pred A
EmptySet x = Empty

Universal : {A : Set} -> Pred A
Universal x = Unit

-- Subset properties
subsetRefl : {A : Set} (P : Pred A) -> P ⊆ P
subsetRefl P x px = px

subsetTrans : {A : Set} {P Q R : Pred A} -> P ⊆ Q -> Q ⊆ R -> P ⊆ R
subsetTrans pq qr x px = qr x (pq x px)

subsetAntiSym : {A : Set} {P Q : Pred A} -> P ⊆ Q -> Q ⊆ P -> SetEq P Q
subsetAntiSym pq qp = pair pq qp

-- Intersection properties
intersectComm : {A : Set} (P Q : Pred A) -> SetEq (P ∩ Q) (Q ∩ P)
intersectComm P Q = pair (\x pq -> pair (snd pq) (fst pq))
                         (\x qp -> pair (snd qp) (fst qp))

intersectAssoc : {A : Set} (P Q R : Pred A) -> SetEq ((P ∩ Q) ∩ R) (P ∩ (Q ∩ R))
intersectAssoc P Q R = pair left right
  where
    left : (P ∩ Q) ∩ R ⊆ P ∩ (Q ∩ R)
    left x (pair (pair px qx) rx) = pair px (pair qx rx)
    right : P ∩ (Q ∩ R) ⊆ (P ∩ Q) ∩ R
    right x (pair px (pair qx rx)) = pair (pair px qx) rx

intersectIdempotent : {A : Set} (P : Pred A) -> SetEq (P ∩ P) P
intersectIdempotent P = pair (\x pp -> fst pp) (\x px -> pair px px)

-- Union properties
unionComm : {A : Set} (P Q : Pred A) -> SetEq (P ∪ Q) (Q ∪ P)
unionComm P Q = pair left right
  where
    left : P ∪ Q ⊆ Q ∪ P
    left x (inl px) = inr px
    left x (inr qx) = inl qx
    right : Q ∪ P ⊆ P ∪ Q
    right x (inl qx) = inr qx
    right x (inr px) = inl px

unionAssoc : {A : Set} (P Q R : Pred A) -> SetEq ((P ∪ Q) ∪ R) (P ∪ (Q ∪ R))
unionAssoc P Q R = pair left right
  where
    left : (P ∪ Q) ∪ R ⊆ P ∪ (Q ∪ R)
    left x (inl (inl px)) = inl px
    left x (inl (inr qx)) = inr (inl qx)
    left x (inr rx) = inr (inr rx)
    right : P ∪ (Q ∪ R) ⊆ (P ∪ Q) ∪ R
    right x (inl px) = inl (inl px)
    right x (inr (inl qx)) = inl (inr qx)
    right x (inr (inr rx)) = inr rx

unionIdempotent : {A : Set} (P : Pred A) -> SetEq (P ∪ P) P
unionIdempotent P = pair left right
  where
    left : P ∪ P ⊆ P
    left x (inl px) = px
    left x (inr px) = px
    right : P ⊆ P ∪ P
    right x px = inl px

-- Distributive laws
distribIntersectUnion : {A : Set} (P Q R : Pred A) -> SetEq (P ∩ (Q ∪ R)) ((P ∩ Q) ∪ (P ∩ R))
distribIntersectUnion P Q R = pair left right
  where
    left : P ∩ (Q ∪ R) ⊆ (P ∩ Q) ∪ (P ∩ R)
    left x (pair px (inl qx)) = inl (pair px qx)
    left x (pair px (inr rx)) = inr (pair px rx)
    right : (P ∩ Q) ∪ (P ∩ R) ⊆ P ∩ (Q ∪ R)
    right x (inl (pair px qx)) = pair px (inl qx)
    right x (inr (pair px rx)) = pair px (inr rx)

distribUnionIntersect : {A : Set} (P Q R : Pred A) -> SetEq (P ∪ (Q ∩ R)) ((P ∪ Q) ∩ (P ∪ R))
distribUnionIntersect P Q R = pair left right
  where
    left : P ∪ (Q ∩ R) ⊆ (P ∪ Q) ∩ (P ∪ R)
    left x (inl px) = pair (inl px) (inl px)
    left x (inr (pair qx rx)) = pair (inr qx) (inr rx)
    right : (P ∪ Q) ∩ (P ∪ R) ⊆ P ∪ (Q ∩ R)
    right x (pair (inl px) _) = inl px
    right x (pair _ (inl px)) = inl px
    right x (pair (inr qx) (inr rx)) = inr (pair qx rx)

-- De Morgan's laws
deMorganUnion : {A : Set} (P Q : Pred A) -> SetEq (Compl (P ∪ Q)) (Compl P ∩ Compl Q)
deMorganUnion P Q = pair left right
  where
    left : Compl (P ∪ Q) ⊆ (Compl P ∩ Compl Q)
    left x notPQ = pair (\px -> notPQ (inl px)) (\qx -> notPQ (inr qx))
    right : (Compl P ∩ Compl Q) ⊆ Compl (P ∪ Q)
    right x (pair notP notQ) (inl px) = notP px
    right x (pair notP notQ) (inr qx) = notQ qx

deMorganIntersect : {A : Set} (P Q : Pred A) -> (Compl P ∪ Compl Q) ⊆ Compl (P ∩ Q)
deMorganIntersect P Q x (inl notP) (pair px qx) = notP px
deMorganIntersect P Q x (inr notQ) (pair px qx) = notQ qx

-- Double complement (requires classical logic for full equivalence)
doubleComplSubset : {A : Set} (P : Pred A) -> P ⊆ Compl (Compl P)
doubleComplSubset P x px notPx = notPx px

-- Absorption laws
absorpUnion : {A : Set} (P Q : Pred A) -> SetEq (P ∪ (P ∩ Q)) P
absorpUnion P Q = pair left right
  where
    left : P ∪ (P ∩ Q) ⊆ P
    left x (inl px) = px
    left x (inr (pair px qx)) = px
    right : P ⊆ P ∪ (P ∩ Q)
    right x px = inl px

absorpIntersect : {A : Set} (P Q : Pred A) -> SetEq (P ∩ (P ∪ Q)) P
absorpIntersect P Q = pair left right
  where
    left : P ∩ (P ∪ Q) ⊆ P
    left x (pair px _) = px
    right : P ⊆ P ∩ (P ∪ Q)
    right x px = pair px (inl px)

-- Identity laws
unionEmpty : {A : Set} (P : Pred A) -> SetEq (P ∪ EmptySet) P
unionEmpty P = pair left right
  where
    left : P ∪ EmptySet ⊆ P
    left x (inl px) = px
    left x (inr ())
    right : P ⊆ P ∪ EmptySet
    right x px = inl px

intersectUniversal : {A : Set} (P : Pred A) -> SetEq (P ∩ Universal) P
intersectUniversal P = pair (\x pq -> fst pq) (\x px -> pair px unit)

-- Annihilation laws
unionUniversal : {A : Set} (P : Pred A) -> Universal ⊆ (P ∪ Universal)
unionUniversal P x u = inr u

intersectEmpty : {A : Set} (P : Pred A) -> SetEq (P ∩ EmptySet) EmptySet
intersectEmpty P = pair (\x pq -> snd pq) (\x e -> absurd e)

-- Set difference properties
setDiffAsIntersect : {A : Set} (P Q : Pred A) -> SetEq (P ∖ Q) (P ∩ Compl Q)
setDiffAsIntersect P Q = pair (\x pq -> pq) (\x pq -> pq)

setDiffSubset : {A : Set} (P Q : Pred A) -> (P ∖ Q) ⊆ P
setDiffSubset P Q x (pair px notQx) = px

-- Power set definition (as type of predicates)
PowerSet : Set -> Set
PowerSet A = Pred A

-- Power set membership
_∈P_ : {A : Set} -> Pred A -> PowerSet A -> Set
P ∈P S = P ⊆ S

-- ============================================
-- CARTESIAN PRODUCTS AND DISJOINT UNIONS
-- ============================================

-- Product of sets (already available as Pair)
-- A × B = { (a, b) | a ∈ A, b ∈ B }

-- Projections
proj₁ : {A B : Set} -> Pair A B -> A
proj₁ = fst

proj₂ : {A B : Set} -> Pair A B -> B
proj₂ = snd

-- Product is associative (up to isomorphism)
prodAssocTo : {A B C : Set} -> Pair (Pair A B) C -> Pair A (Pair B C)
prodAssocTo (pair (pair a b) c) = pair a (pair b c)

prodAssocFrom : {A B C : Set} -> Pair A (Pair B C) -> Pair (Pair A B) C
prodAssocFrom (pair a (pair b c)) = pair (pair a b) c

-- Product is commutative (up to isomorphism)
prodCommTo : {A B : Set} -> Pair A B -> Pair B A
prodCommTo (pair a b) = pair b a

-- Disjoint union is associative
sumAssocTo : {A B C : Set} -> Sum (Sum A B) C -> Sum A (Sum B C)
sumAssocTo (inl (inl a)) = inl a
sumAssocTo (inl (inr b)) = inr (inl b)
sumAssocTo (inr c) = inr (inr c)

sumAssocFrom : {A B C : Set} -> Sum A (Sum B C) -> Sum (Sum A B) C
sumAssocFrom (inl a) = inl (inl a)
sumAssocFrom (inr (inl b)) = inl (inr b)
sumAssocFrom (inr (inr c)) = inr c

-- Disjoint union is commutative
sumCommTo : {A B : Set} -> Sum A B -> Sum B A
sumCommTo (inl a) = inr a
sumCommTo (inr b) = inl b

-- ============================================
-- BOOLEAN ALGEBRA STRUCTURE
-- ============================================

{-
  Sets under ∪, ∩, and complement form a Boolean algebra!

  A Boolean algebra satisfies:
  1. Associativity of ∪ and ∩
  2. Commutativity of ∪ and ∩
  3. Distributivity in both directions
  4. Identity elements (∅ for ∪, U for ∩)
  5. Complement laws

  We've already proven 1-4 above. The complement laws:
  - P ∪ (Compl P) = U    (Law of Excluded Middle - requires classical logic)
  - P ∩ (Compl P) = ∅    (Non-contradiction)
-}

-- Non-contradiction is provable constructively
nonContradiction : {A : Set} (P : Pred A) -> SetEq (P ∩ Compl P) EmptySet
nonContradiction P = pair left right
  where
    left : (P ∩ Compl P) ⊆ EmptySet
    left x (pair px notPx) = notPx px
    right : EmptySet ⊆ (P ∩ Compl P)
    right x e = absurd e

-- Excluded middle would require classical logic
-- LEM : {A : Set} (P : Pred A) -> SetEq (P ∪ Compl P) Universal

-- ============================================
-- CARDINALITY (Finite Sets)
-- ============================================

-- Finite set as a function from Fin n
FinSet : Nat -> Set -> Set
FinSet n A = Fin n -> A

-- Cardinality of finite set represented by list
card : {A : Set} -> List A -> Nat
card = length

-- ============================================
-- EXERCISES
-- ============================================

{-
  EXERCISE 1: Prove that subset is transitive
  (This is already proved above, but try it yourself!)
-}
exercise-subsetTrans : {A : Set} {P Q R : Pred A} -> P ⊆ Q -> Q ⊆ R -> P ⊆ R
exercise-subsetTrans pq qr x px = qr x (pq x px)

{-
  EXERCISE 2: Prove that the empty set is a subset of every set
-}
exercise-emptySubset : {A : Set} (P : Pred A) -> EmptySet ⊆ P
exercise-emptySubset P x ()

{-
  EXERCISE 3: Prove that every set is a subset of the universal set
-}
exercise-subsetUniversal : {A : Set} (P : Pred A) -> P ⊆ Universal
exercise-subsetUniversal P x px = unit

{-
  EXERCISE 4: Prove intersection is monotonic in both arguments
  If P ⊆ P' and Q ⊆ Q', then (P ∩ Q) ⊆ (P' ∩ Q')
-}
exercise-intersectMono : {A : Set} {P P' Q Q' : Pred A} ->
  P ⊆ P' -> Q ⊆ Q' -> (P ∩ Q) ⊆ (P' ∩ Q')
exercise-intersectMono pp' qq' x (pair px qx) = pair (pp' x px) (qq' x qx)

{-
  EXERCISE 5: Prove union is monotonic in both arguments
-}
exercise-unionMono : {A : Set} {P P' Q Q' : Pred A} ->
  P ⊆ P' -> Q ⊆ Q' -> (P ∪ Q) ⊆ (P' ∪ Q')
exercise-unionMono pp' qq' x (inl px) = inl (pp' x px)
exercise-unionMono pp' qq' x (inr qx) = inr (qq' x qx)

{-
  EXERCISE 6: Prove that intersection is the greatest lower bound
  P ∩ Q ⊆ P, P ∩ Q ⊆ Q, and if R ⊆ P and R ⊆ Q then R ⊆ P ∩ Q
-}
exercise-intersectGLB : {A : Set} {P Q R : Pred A} ->
  R ⊆ P -> R ⊆ Q -> R ⊆ (P ∩ Q)
exercise-intersectGLB rp rq x rx = pair (rp x rx) (rq x rx)

{-
  EXERCISE 7: Prove that union is the least upper bound
  P ⊆ P ∪ Q, Q ⊆ P ∪ Q, and if P ⊆ R and Q ⊆ R then P ∪ Q ⊆ R
-}
exercise-unionLUB : {A : Set} {P Q R : Pred A} ->
  P ⊆ R -> Q ⊆ R -> (P ∪ Q) ⊆ R
exercise-unionLUB pr qr x (inl px) = pr x px
exercise-unionLUB pr qr x (inr qx) = qr x qx

{-
  EXERCISE 8: Prove that set difference satisfies P ∖ Q ⊆ P
-}
exercise-diffSubset : {A : Set} (P Q : Pred A) -> (P ∖ Q) ⊆ P
exercise-diffSubset P Q x (pair px notQx) = px

{-
  EXERCISE 9: Prove that if P and Q are disjoint, then P ⊆ Compl Q
  Disjoint means P ∩ Q = ∅
-}
postulate
  exercise-disjointCompl : {A : Set} {P Q : Pred A} ->
    SetEq (P ∩ Q) EmptySet -> P ⊆ Compl Q

{-
  EXERCISE 10 (Challenge): Prove the symmetric difference is associative
  P △ Q = (P ∖ Q) ∪ (Q ∖ P)
-}
SymDiff : {A : Set} -> Pred A -> Pred A -> Pred A
SymDiff P Q = (P ∖ Q) ∪ (Q ∖ P)

postulate
  exercise-symDiffAssoc : {A : Set} (P Q R : Pred A) ->
    SetEq (SymDiff (SymDiff P Q) R) (SymDiff P (SymDiff Q R))
