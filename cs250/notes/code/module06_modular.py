"""
Module 6 — Modular Arithmetic
Runnable Python companion to CS 250 Module 6.

Contains:
- mod_inverse(a, n): brute-force multiplicative inverse mod n
  (Module 6 Exercise 13).
- A simple Chinese Remainder Theorem solver by enumeration.
"""


def mod_inverse(a, n):
    """Return the multiplicative inverse of a mod n, or None if it doesn't exist.

    Brute force: try every x in {0, ..., n-1} and return the first one
    satisfying a*x ≡ 1 (mod n). See module07_hoare.py for the faster
    extended-Euclidean version.
    """
    for x in range(n):
        if (a * x) % n == 1:
            return x
    return None


def crt_two(r1, m1, r2, m2):
    """Find the unique x mod m1*m2 with x ≡ r1 (mod m1) and x ≡ r2 (mod m2).

    Assumes gcd(m1, m2) = 1. Returns x in the range [0, m1*m2).
    """
    for x in range(m1 * m2):
        if x % m1 == r1 and x % m2 == r2:
            return x
    raise ValueError("no solution (m1 and m2 must be coprime)")


def crt_many(residues_and_moduli):
    """Chinese Remainder Theorem for a list of (residue, modulus) pairs.

    Reduces pairwise via crt_two. Assumes all moduli are pairwise coprime.
    """
    r, m = residues_and_moduli[0]
    for ri, mi in residues_and_moduli[1:]:
        r = crt_two(r, m, ri, mi)
        m = m * mi
        r = r % m
    return r, m


def demo():
    # Module 6 Exercise 13 test cases
    assert mod_inverse(3, 7) == 5      # 3 * 5 = 15 ≡ 1 (mod 7)
    assert mod_inverse(2, 6) is None   # gcd(2, 6) = 2, no inverse
    assert mod_inverse(1, 5) == 1
    assert mod_inverse(4, 7) == 2      # 4 * 2 = 8 ≡ 1 (mod 7)

    # Every nonzero residue mod 7 (prime) has an inverse
    for a in range(1, 7):
        inv = mod_inverse(a, 7)
        assert inv is not None
        assert (a * inv) % 7 == 1

    # In Z/8Z, even numbers have no inverse
    for a in [2, 4, 6]:
        assert mod_inverse(a, 8) is None
    for a in [1, 3, 5, 7]:
        assert mod_inverse(a, 8) is not None

    # CRT: the classic Sunzi puzzle from Module 6
    # x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7)
    x, m = crt_many([(2, 3), (3, 5), (2, 7)])
    assert x == 23
    assert m == 105

    # Module 6 Exercise 10: x ≡ 1 (mod 4), x ≡ 2 (mod 9), x ≡ 3 (mod 25)
    x2, m2 = crt_many([(1, 4), (2, 9), (3, 25)])
    assert x2 == 353
    assert m2 == 900

    print("OK")


if __name__ == "__main__":
    demo()
