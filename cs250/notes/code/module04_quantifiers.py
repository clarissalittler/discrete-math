"""
Module 4 — Predicate Logic
Runnable Python companion to CS 250 Module 4.

Contains:
- forall_exists(P, A, B): checks the statement ∀a ∈ A. ∃b ∈ B. P(a, b).
- exists_forall(P, A, B): checks the statement ∃b ∈ B. ∀a ∈ A. P(a, b).
- Demonstration that quantifier order matters (Module 4 Exercise 13).
"""


def forall_exists(P, A, B):
    """True iff for every a in A there is some b in B with P(a, b)."""
    return all(any(P(a, b) for b in B) for a in A)


def exists_forall(P, A, B):
    """True iff there is some b in B with P(a, b) for every a in A."""
    return any(all(P(a, b) for a in A) for b in B)


def demo():
    # Module 4 Exercise 13: the split-witnesses predicate
    # P(a, b) = (a + b == 3) on A = B = {0, 1, 2, 3}
    A = B = {0, 1, 2, 3}
    P = lambda a, b: a + b == 3

    # For every a, pick b = 3 - a -> True
    assert forall_exists(P, A, B) is True
    # No single b works for every a simultaneously -> False
    assert exists_forall(P, A, B) is False

    # A case where both are True: P(a, b) = (a + b <= 10) on small ints
    Q = lambda a, b: a + b <= 10
    assert forall_exists(Q, A, B) is True
    # b = 0 works for every a (since every a is at most 3 <= 10)
    assert exists_forall(Q, A, B) is True

    # A case where both are False: P(a, b) = (a == b + 1) on {0, 1}
    R = lambda a, b: a == b + 1
    # a = 0 has no b in {0, 1} with 0 = b + 1 (would need b = -1)
    assert forall_exists(R, {0, 1}, {0, 1}) is False
    # No single b satisfies a == b + 1 for every a in {0, 1}
    assert exists_forall(R, {0, 1}, {0, 1}) is False

    print("OK")


if __name__ == "__main__":
    demo()
