"""
Module 8 — Sequences and Induction
Runnable Python companion to CS 250 Module 8.

Contains:
- sum_of_squares(n): recursive implementation matching the induction
  proof of sum_{i=1}^n i^2 = n(n+1)(2n+1)/6 (Module 8 Exercise 12).
- fib_rec / fib_iter / fib_memo: three implementations of Fibonacci
  for the recursion-vs-iteration-vs-memoization comparison
  (Module 8 Exercise 13).
"""

from functools import lru_cache


def sum_of_squares(n):
    """Recursive sum of squares, mirroring the induction proof.

    The shape of this function is exactly the shape of the induction
    proof: base case n = 0 returns 0; recursive case adds n^2 to the
    result of the recursive call. The 'if n == 0: return 0' is the
    proof's base case; 'sum_of_squares(n - 1)' is the inductive
    hypothesis; '+ n*n' is the inductive step.
    """
    if n == 0:
        return 0
    return sum_of_squares(n - 1) + n * n


def fib_rec(n):
    """Naive recursive Fibonacci. O(phi^n) time, terrible but faithful to the math."""
    if n < 2:
        return n
    return fib_rec(n - 1) + fib_rec(n - 2)


def fib_iter(n):
    """Iterative Fibonacci. O(n) time, O(1) extra space."""
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


@lru_cache(maxsize=None)
def fib_memo(n):
    """Memoized recursive Fibonacci. O(n) time after warmup; O(n) space."""
    if n < 2:
        return n
    return fib_memo(n - 1) + fib_memo(n - 2)


def demo():
    # Sum of squares against the closed form n*(n+1)*(2n+1)/6
    for n in range(15):
        expected = n * (n + 1) * (2 * n + 1) // 6
        assert sum_of_squares(n) == expected, (n, sum_of_squares(n), expected)

    # Three Fibonacci implementations should agree on small inputs
    for i in range(11):
        assert fib_rec(i) == fib_iter(i) == fib_memo(i)

    # Known Fibonacci values
    assert fib_iter(10) == 55
    assert fib_iter(20) == 6765

    # Memoized version is fast enough to compute fib(50) in the blink of an eye
    assert fib_memo(50) == 12586269025

    print("OK")


if __name__ == "__main__":
    demo()
