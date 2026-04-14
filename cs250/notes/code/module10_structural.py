"""
Module 10 — Structural Induction
Runnable Python companion to CS 250 Module 10.

Contains:
- List and BinTree implementations following the BNF definitions
  List A := Nil | Cons(A, List A)
  BinTree := Leaf | Node(BinTree, BinTree)
- Recursive functions on both datatypes: length, append, reverse,
  size, edges, leaves, height.
- Property-based smoke tests for the theorems proved in Module 10
  by structural induction (Module 10 Exercise 11).
"""

import random
from dataclasses import dataclass


# --- Lists (BNF: List A := Nil | Cons(A, List A)) ---

class Nil:
    def __repr__(self):
        return "Nil"


NIL = Nil()


@dataclass
class Cons:
    head: object
    tail: object


def length(xs):
    """length(Nil) = 0; length(Cons(x, xs')) = 1 + length(xs')."""
    if isinstance(xs, Nil):
        return 0
    return 1 + length(xs.tail)


def append(xs, ys):
    """Nil ++ ys = ys; Cons(x, xs') ++ ys = Cons(x, xs' ++ ys)."""
    if isinstance(xs, Nil):
        return ys
    return Cons(xs.head, append(xs.tail, ys))


def reverse(xs):
    """reverse(Nil) = Nil; reverse(Cons(x, xs')) = reverse(xs') ++ Cons(x, Nil)."""
    if isinstance(xs, Nil):
        return NIL
    return append(reverse(xs.tail), Cons(xs.head, NIL))


def list_eq(xs, ys):
    """Structural equality on lists."""
    if isinstance(xs, Nil) and isinstance(ys, Nil):
        return True
    if isinstance(xs, Nil) or isinstance(ys, Nil):
        return False
    return xs.head == ys.head and list_eq(xs.tail, ys.tail)


def from_pylist(items):
    out = NIL
    for x in reversed(items):
        out = Cons(x, out)
    return out


# --- Binary trees (BNF: BinTree := Leaf | Node(BinTree, BinTree)) ---

class Leaf:
    def __repr__(self):
        return "Leaf"


LEAF = Leaf()


@dataclass
class Node:
    left: object
    right: object


def size(t):
    """size(Leaf) = 0; size(Node(l, r)) = 1 + size(l) + size(r)."""
    if isinstance(t, Leaf):
        return 0
    return 1 + size(t.left) + size(t.right)


def edges(t):
    """edges(Leaf) = 0; edges(Node(l, r)) = 2 + edges(l) + edges(r)."""
    if isinstance(t, Leaf):
        return 0
    return 2 + edges(t.left) + edges(t.right)


def leaves(t):
    """leaves(Leaf) = 1; leaves(Node(l, r)) = leaves(l) + leaves(r)."""
    if isinstance(t, Leaf):
        return 1
    return leaves(t.left) + leaves(t.right)


def height(t):
    """height(Leaf) = 0; height(Node(l, r)) = 1 + max(height l, height r)."""
    if isinstance(t, Leaf):
        return 0
    return 1 + max(height(t.left), height(t.right))


# --- Random generators for property-based smoke tests ---

def random_list(rng, n):
    xs = NIL
    for _ in range(n):
        xs = Cons(rng.randint(0, 99), xs)
    return xs


def random_tree(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return LEAF
    return Node(random_tree(rng, depth - 1), random_tree(rng, depth - 1))


def demo():
    # length(Cons(a, Cons(b, Nil))) = 2 (Module 10 Exercise 2)
    assert length(Cons("a", Cons("b", NIL))) == 2

    # Append a three-element list with a one-element list
    xs = from_pylist([1, 2])
    ys = from_pylist([3])
    xys = append(xs, ys)
    assert list_eq(xys, from_pylist([1, 2, 3]))

    # reverse is an involution (Module 10 Exercise 8)
    for items in [[], [1], [1, 2], [1, 2, 3], [1, 2, 3, 4, 5]]:
        xs = from_pylist(items)
        assert list_eq(reverse(reverse(xs)), xs), items

    # size of the worked-example tree from the module
    # Node(Leaf, Node(Leaf, Leaf)) -> size 2, edges 4, leaves 3
    t = Node(LEAF, Node(LEAF, LEAF))
    assert size(t) == 2
    assert edges(t) == 4
    assert leaves(t) == size(t) + 1  # Exercise 4: leaves = size + 1

    # Property-based: run a bunch of random tests for the main theorems
    rng = random.Random(42)  # fixed seed for reproducibility

    # length(xs ++ ys) = length(xs) + length(ys)
    for _ in range(100):
        a = random_list(rng, rng.randint(0, 10))
        b = random_list(rng, rng.randint(0, 10))
        assert length(append(a, b)) == length(a) + length(b)

    # length(reverse(xs)) = length(xs) and reverse is an involution
    for _ in range(100):
        a = random_list(rng, rng.randint(0, 10))
        assert length(reverse(a)) == length(a)
        assert list_eq(reverse(reverse(a)), a)

    # edges(t) = 2 * size(t) for any binary tree
    for _ in range(100):
        tr = random_tree(rng, 5)
        assert edges(tr) == 2 * size(tr)

    # leaves(t) = size(t) + 1
    for _ in range(100):
        tr = random_tree(rng, 5)
        assert leaves(tr) == size(tr) + 1

    print("OK")


if __name__ == "__main__":
    demo()
