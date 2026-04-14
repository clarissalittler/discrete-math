"""
Module 3 — Proof Systems and Digital Logic
Runnable Python companion to CS 250 Module 3.

Contains:
- dnf(f, n): mechanical DNF-formula generator from a boolean function
  (Module 3 Exercise 13).
- NAND-only reconstructions of NOT, AND, OR (Module 2 Exercise 8 and the
  functional-completeness discussion in Module 3).
"""

from itertools import product


def dnf(f, n):
    """Return a DNF formula string equivalent to f.

    The recipe is: for every input row where f is True, emit a conjunction
    of literals (x_i if that variable was True in the row, not x_i if it
    was False). Then OR all the conjunctions together.
    """
    var_names = [f"x{i}" for i in range(n)]
    terms = []
    for assignment in product([False, True], repeat=n):
        if f(*assignment):
            literals = [
                name if val else f"not {name}"
                for name, val in zip(var_names, assignment)
            ]
            terms.append("(" + " and ".join(literals) + ")")
    if not terms:
        return "False"
    return " or ".join(terms)


# NAND-only reconstructions (Module 2 Exercise 8)
def nand(p, q):
    return not (p and q)


def not_from_nand(p):
    return nand(p, p)


def and_from_nand(p, q):
    inner = nand(p, q)
    return nand(inner, inner)


def or_from_nand(p, q):
    # p or q = not (not p and not q) = nand(nand(p,p), nand(q,q))
    return nand(nand(p, p), nand(q, q))


def demo():
    # Module 3 Exercise 13: DNF for XOR on two variables
    xor_dnf = dnf(lambda x0, x1: x0 != x1, 2)
    # Two T rows -> two disjuncts
    assert xor_dnf.count(" or ") == 1
    assert "not x0" in xor_dnf and "not x1" in xor_dnf

    # Exactly-one function on three variables (Module 2 Exercise 9)
    def exactly_one(x, y, z):
        return (
            (x and not y and not z)
            or (not x and y and not z)
            or (not x and not y and z)
        )

    three_dnf = dnf(exactly_one, 3)
    # Three T rows -> two 'or' separators -> three disjuncts
    assert three_dnf.count(" or ") == 2

    # Contradiction gives "False"
    assert dnf(lambda x, y: x and not x, 2) == "False"

    # NAND completeness: verify that the NAND-only versions agree with
    # the built-in Python boolean operators on every input (Module 2 Ex. 8)
    for p, q in product([False, True], repeat=2):
        assert not_from_nand(p) == (not p)
        assert and_from_nand(p, q) == (p and q)
        assert or_from_nand(p, q) == (p or q)

    print("OK")


if __name__ == "__main__":
    demo()
