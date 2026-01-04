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
