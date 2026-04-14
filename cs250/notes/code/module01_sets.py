"""
Module 1 — Sets and Functions
Runnable Python companion to CS 250 Module 1.

Contains:
- cartesian(xs, ys): from-scratch Cartesian product (Module 1 Exercise 13).
- A small demonstration of basic set operations using Python's built-in set type.
"""


def cartesian(xs, ys):
    """Cartesian product of two lists as a list of tuples.

    Equivalent to list(itertools.product(xs, ys)) but implemented from
    scratch with a nested loop so the algorithmic content is explicit.

    Given xs of length m and ys of length n, does exactly m * n work.
    This is the computational content of |A x B| = |A| * |B|.
    """
    result = []
    for x in xs:
        for y in ys:
            result.append((x, y))
    return result


def demo():
    # Module 1 Exercise 13: cartesian([1, 2], ['a', 'b', 'c'])
    out = cartesian([1, 2], ['a', 'b', 'c'])
    assert out == [
        (1, 'a'), (1, 'b'), (1, 'c'),
        (2, 'a'), (2, 'b'), (2, 'c'),
    ], out
    assert len(out) == 2 * 3

    # Basic set operations (Module 1)
    A = {1, 2, 3, 4}
    B = {3, 4, 5, 6}
    assert A & B == {3, 4}              # intersection
    assert A | B == {1, 2, 3, 4, 5, 6}  # union
    assert A - B == {1, 2}              # difference
    assert len(cartesian(list(A), list(B))) == 16  # |A x B|

    # The power-set size formula: 2^n
    def powerset(s):
        items = list(s)
        n = len(items)
        return [
            {items[i] for i in range(n) if (mask >> i) & 1}
            for mask in range(1 << n)
        ]

    assert len(powerset({1, 2, 3})) == 8
    print("OK")


if __name__ == "__main__":
    demo()
