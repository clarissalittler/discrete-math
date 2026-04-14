"""
Module 2 — Propositional Logic
Runnable Python companion to CS 250 Module 2.

Contains:
- is_tautology(f, n): brute-force tautology checker (Module 2 Exercise 13).
- truth_table(f, n, names): build and print a truth table for a formula.
- Classification of formulas as tautology / contradiction / contingent.
"""

from itertools import product


def is_tautology(f, n):
    """True iff f returns True on every assignment to its n boolean arguments.

    >>> is_tautology(lambda p, q: (not p) or q, 2)      # p -> q
    False
    >>> is_tautology(lambda p, q: p or (not p), 2)       # p v ~p
    True
    """
    return all(f(*assignment) for assignment in product([False, True], repeat=n))


def is_contradiction(f, n):
    """True iff f returns False on every assignment."""
    return all(not f(*assignment) for assignment in product([False, True], repeat=n))


def classify(f, n):
    """Return 'tautology', 'contradiction', or 'contingent'."""
    if is_tautology(f, n):
        return "tautology"
    if is_contradiction(f, n):
        return "contradiction"
    return "contingent"


def truth_table(f, n, names=None):
    """Build a truth table for f as a list of (assignment, output) pairs."""
    if names is None:
        names = [f"x{i}" for i in range(n)]
    rows = []
    for assignment in product([False, True], repeat=n):
        rows.append((assignment, f(*assignment)))
    return rows


def print_truth_table(f, n, names=None, label="f"):
    if names is None:
        names = [f"x{i}" for i in range(n)]
    print(" ".join(f"{name:5}" for name in names) + f" | {label}")
    print("-" * (6 * n + 3 + len(label)))
    for assignment, output in truth_table(f, n, names):
        cells = " ".join(f"{'T' if v else 'F':5}" for v in assignment)
        print(f"{cells} | {'T' if output else 'F'}")


def demo():
    # Module 2 Exercise 13: tautology checker
    assert is_tautology(lambda p, q: (not p) or q, 2) is False
    assert is_tautology(lambda p, q: p or (not p), 2) is True

    # Module 2 Exercise 4: classify formulas
    assert classify(lambda p: p or (not p), 1) == "tautology"
    assert classify(lambda p: p and (not p), 1) == "contradiction"
    assert classify(lambda p, q: p and q, 2) == "contingent"
    # (p -> q) is contingent (not a tautology)
    assert classify(lambda p, q: (not p) or q, 2) == "contingent"
    # ((p & q) -> (p | q)) is a tautology
    assert classify(lambda p, q: (not (p and q)) or (p or q), 2) == "tautology"

    # De Morgan's laws: the two sides should have the same truth table
    lhs = lambda p, q: not (p and q)
    rhs = lambda p, q: (not p) or (not q)
    for a in product([False, True], repeat=2):
        assert lhs(*a) == rhs(*a), a

    # Print the classic implication truth table as a smoke test
    print("Truth table for p -> q (i.e., ~p v q):")
    print_truth_table(lambda p, q: (not p) or q, 2, ["p", "q"], label="p->q")
    print("OK")


if __name__ == "__main__":
    demo()
