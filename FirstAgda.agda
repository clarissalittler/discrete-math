module FirstAgda where

data ⊤ : Set where
  tt : ⊤

lemma-1 : {A : Set} -> (⊤ -> A) -> A
lemma-1 p = p tt

data ⊥ : Set where

lemma-2 : {A : Set} -> ⊥ -> A
lemma-2 ()

data Nat : Set where
  z : Nat
  s : Nat -> Nat

_+_ : Nat -> Nat -> Nat
z + n2 = n2
s n1 + n2 = s (n1 + n2)

data Vec (A : Set) : Nat -> Set where
  empty : Vec A z
  cons  : ∀ {n : Nat} -> A -> Vec A n -> Vec A (s n)

pop : {A : Set} {n : Nat} -> Vec A (s n) -> A
pop (cons x v) = x

data _≡_ {A : Set} : A -> A -> Set where
  refl : {a : A} -> a ≡ a

{-
  We need some more properties of the idea of ≡ and we need to start with showing that it's a equivalence relation

  we have reflexivity by default
  but what about transitivity and symmetry
-}

≡-sym : ∀ {A : Set} {a1 a2 : A} -> (a1 ≡ a2) -> (a2 ≡ a1)
≡-sym refl = refl

≡-trans : {A : Set} {a1 a2 a3 : A} -> (a1 ≡ a2) -> (a2 ≡ a3) -> a1 ≡ a3
≡-trans refl p23 = p23

cong : {A B : Set} {a1 a2 : A}
  -> (f : A -> B) -> a1 ≡ a2 -> (f a1) ≡ (f a2)
cong f refl = refl

add-zero : (n : Nat) -> (z + n) ≡ n
add-zero n = refl

-- proof a by induction where P(0) is the trivial
-- case and P(s n) is proved by using P(n)
-- that's what the recursive call to add-zero-2 is
add-zero-2 : (n : Nat) -> (n + z) ≡ n
add-zero-2 z = refl
add-zero-2 (s n) = cong s (add-zero-2 n)

add-succ-l : (n1 n2 : Nat) -> (s n1 + n2) ≡ s (n1 + n2)
add-succ-l n1 n2 = refl

add-succ-r : (n1 n2 : Nat) -> (n1 + (s n2)) ≡ s (n1 + n2)
add-succ-r z n2 = refl
add-succ-r (s n1) n2 = cong s (add-succ-r n1 n2)
{-
 s n1 + s n2 ==> s (n1 + s n2)
   but (n1 + s n2) ===> s (n1 + n2) is just given by add-succ-r n1 n2

   need to show (n1 + (s n2)) = s (n1 + n2)
   if n1 is zero then this becomes s n2 = s (0 + n2) = s n2 ∎
   if n1 = (s n1') then this becomes

  (s n1 + s n2) = s (n1 + s n2) by definition of addition
  and n1 + s n2 = s (n1 + n2) by add-succ n1 n2 (the inductive hypothesis)
  thus s n1 + s n2 = s (s (n1 + n2))
-}


{-

 Let n1 and n2 be natural numbers, we want to prove
 that (n1 + n2) = (n2 + n1)

 Either n1 is zero or it is s (n1') where n1' is another natural number.
 Case n1 = 0.
   We need to show that (0 + n2) = (n2 + 0)
   (0 + n2) = n2 = (n2 + 0)
   ∎

 Case n1 = s n1'
  the goal becomes (s n1' + n2) = (n2 + s n1')
  we have as a inductive hypothesis that n1' + n2 = n2 + n1'
  the left hand side is just s (n1' + n2) = s (n2 + n1') = n2 + s n1'
  ∎

-}
+-commut : (n1 n2 : Nat) -> (n1 + n2) ≡ (n2 + n1)
+-commut z n2 = ≡-trans (add-zero n2) (≡-sym (add-zero-2 n2))
+-commut (s n1) n2 = ≡-trans (add-succ-l n1 n2)
                    (≡-sym (≡-trans (add-succ-r n2 n1) (cong s (+-commut n2 n1))))

