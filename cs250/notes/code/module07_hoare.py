"""
Module 7 — Indirect Proof, Euclidean Algorithm, Hoare Logic
Runnable Python companion to CS 250 Module 7.

Contains:
- gcd(a, b): Euclid's algorithm (Module 7 Section on GCD).
- egcd(a, b): extended Euclidean algorithm (Module 7 Exercise 12).
- mod_inverse_via_egcd(a, n): fast modular inverse using egcd.
- An implementation of the sum-to-n program whose Hoare-logic correctness
  is proved in the module's worked while-loop example.
"""


def gcd(a, b):
    """Non-negative gcd via Euclid's algorithm."""
    a, b = abs(a), abs(b)
    while b:
        a, b = b, a % b
    return a


def egcd(a, b):
    """Extended Euclidean algorithm.

    Returns (g, x, y) with g = gcd(a, b) and a*x + b*y = g.
    """
    if b == 0:
        return (a, 1, 0)
    g, x1, y1 = egcd(b, a % b)
    # g = b*x1 + (a%b)*y1
    # a%b = a - (a//b)*b, so
    # g = b*x1 + (a - (a//b)*b)*y1 = a*y1 + b*(x1 - (a//b)*y1)
    return (g, y1, x1 - (a // b) * y1)


def mod_inverse_via_egcd(a, n):
    """Multiplicative inverse of a mod n, or raise ValueError if it doesn't exist.

    Logarithmic in n, unlike the O(n) brute force in module06_modular.py.
    """
    g, x, _ = egcd(a % n, n)
    if g != 1:
        raise ValueError(f"{a} has no inverse mod {n} (gcd is {g})")
    return x % n


def sum_to_n(n):
    """Computes 0 + 1 + ... + n using the program from the worked while-loop proof.

    The Hoare-logic proof in Module 7 shows that this implementation is
    partially correct under the invariant s = i*(i+1)/2 & 0 ≤ i ≤ n.
    """
    assert n >= 0
    i = 0
    s = 0
    while i < n:
        i = i + 1
        s = s + i
    return s


def demo():
    # Module 7 Exercise 2: trace gcd(48, 18)
    assert gcd(48, 18) == 6
    assert gcd(1024, 1536) == 512
    assert gcd(21, 35) == 7
    assert gcd(17, 5) == 1

    # Module 7 Exercise 8: extended Euclidean for (17, 5) -> Bezout
    g, x, y = egcd(17, 5)
    assert g == 1
    assert 17 * x + 5 * y == 1

    # Exercise 12: modular inverse via egcd matches brute-force version
    assert mod_inverse_via_egcd(3, 7) == 5
    assert mod_inverse_via_egcd(17, 5) == 3     # 17 * 3 = 51 ≡ 1 (mod 5)
    assert mod_inverse_via_egcd(5, 17) == 7     # 5 * 7 = 35 ≡ 1 (mod 17)

    try:
        mod_inverse_via_egcd(2, 6)
        assert False, "should have raised"
    except ValueError:
        pass

    # Module 7 worked while-loop: sum 0 + 1 + ... + n
    assert sum_to_n(0) == 0
    assert sum_to_n(1) == 1
    assert sum_to_n(5) == 15
    assert sum_to_n(100) == 5050
    # Matches the closed form n*(n+1)/2
    for n in range(20):
        assert sum_to_n(n) == n * (n + 1) // 2

    print("OK")


if __name__ == "__main__":
    demo()
