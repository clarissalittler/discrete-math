"""
Module 9 — Strong Induction and Recurrences
Runnable Python companion to CS 250 Module 9.

Contains:
- fib_closed(n): closed-form Fibonacci using phi and sqrt(5)
  (Module 9 Exercise 11). Exact on small n, floating-point-limited on large n.
- fib_matrix(n): O(log n) Fibonacci via matrix exponentiation
  (Module 9 Exercise 11). Exact thanks to Python's arbitrary-precision ints.
- Linear recurrence solvers for a few specific cases from Module 9 exercises.
- hanoi(n): closed form 2^n - 1 for the Tower of Hanoi (Module 9 Exercise 10).
"""

import math

PHI = (1 + math.sqrt(5)) / 2
PSI = (1 - math.sqrt(5)) / 2


def fib_closed(n):
    """Closed-form Fibonacci using phi, psi, and sqrt(5). Rounds at the end.

    Exact for small n, but accumulates floating-point error as n grows.
    """
    return round((PHI ** n - PSI ** n) / math.sqrt(5))


def fib_iter(n):
    """Iterative Fibonacci for comparison/verification."""
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def _mat_mul(A, B):
    return (
        (A[0][0] * B[0][0] + A[0][1] * B[1][0],
         A[0][0] * B[0][1] + A[0][1] * B[1][1]),
        (A[1][0] * B[0][0] + A[1][1] * B[1][0],
         A[1][0] * B[0][1] + A[1][1] * B[1][1]),
    )


def _mat_pow(M, k):
    if k == 1:
        return M
    half = _mat_pow(M, k // 2)
    full = _mat_mul(half, half)
    return _mat_mul(full, M) if k % 2 else full


def fib_matrix(n):
    """Matrix-exponentiation Fibonacci, O(log n). Uses Python's bigints."""
    if n == 0:
        return 0
    M = ((1, 1), (1, 0))
    return _mat_pow(M, n)[0][1]


# --- Linear recurrence examples from Module 9 ---


def seq_M9_E6(n):
    """Module 9 Exercise 6: a_k = 4 a_{k-1} - 3 a_{k-2}, a_0 = 1, a_1 = 3.

    Characteristic equation (r-1)(r-3) = 0; closed form a_n = 3^n.
    """
    return 3 ** n


def seq_M9_E7(n):
    """Module 9 Exercise 7: a_k = 5 a_{k-1} - 6 a_{k-2}, a_0 = 1, a_1 = 5.

    Characteristic equation (r-2)(r-3) = 0; closed form 3^{n+1} - 2^{n+1}.
    """
    return 3 ** (n + 1) - 2 ** (n + 1)


def seq_M9_E8(n):
    """Module 9 Exercise 8: a_k = 6 a_{k-1} - 9 a_{k-2}, a_0 = 2, a_1 = 12.

    Repeated root r = 3; closed form 2(n+1) * 3^n.
    """
    return 2 * (n + 1) * 3 ** n


def hanoi(n):
    """Closed form for Tower of Hanoi: 2^n - 1 (Module 9 Exercise 10)."""
    return 2 ** n - 1


def _verify_recurrence(seq, recurrence, a0, a1, up_to):
    """Verify that seq matches the given initial conditions and recurrence."""
    assert seq(0) == a0
    assert seq(1) == a1
    for n in range(2, up_to):
        assert seq(n) == recurrence(seq(n - 1), seq(n - 2)), n


def demo():
    # Fibonacci: closed form matches iterative on small inputs
    for n in range(20):
        assert fib_closed(n) == fib_iter(n)

    # Matrix version matches iterative exactly for large n (both exact)
    for n in range(60):
        assert fib_matrix(n) == fib_iter(n)

    assert fib_matrix(50) == 12586269025
    assert fib_matrix(100) == 354224848179261915075

    # Recurrence closed forms agree with direct iteration of the recurrence
    _verify_recurrence(
        seq_M9_E6, lambda p1, p2: 4 * p1 - 3 * p2, 1, 3, up_to=15
    )
    _verify_recurrence(
        seq_M9_E7, lambda p1, p2: 5 * p1 - 6 * p2, 1, 5, up_to=15
    )
    _verify_recurrence(
        seq_M9_E8, lambda p1, p2: 6 * p1 - 9 * p2, 2, 12, up_to=15
    )

    # Tower of Hanoi: H_1 = 1, H_n = 2 H_{n-1} + 1
    assert hanoi(1) == 1
    h_prev = 1
    for n in range(2, 15):
        h = hanoi(n)
        assert h == 2 * h_prev + 1
        h_prev = h

    print("OK")


if __name__ == "__main__":
    demo()
