"""
Module 5 — Direct Proof and Groups
Runnable Python companion to CS 250 Module 5.

Contains:
- is_group(carrier, op, identity): exhaustive group axiom checker
  (Module 5 Exercise 13). This is proof by exhaustion, automated.
"""


def is_group(carrier, op, identity):
    """Check by brute force whether (carrier, op, identity) is a group.

    Verifies closure, associativity, left/right identity, and
    existence of two-sided inverses for every element.
    """
    # Closure
    for a in carrier:
        for b in carrier:
            if op(a, b) not in carrier:
                return False
    # Associativity
    for a in carrier:
        for b in carrier:
            for c in carrier:
                if op(op(a, b), c) != op(a, op(b, c)):
                    return False
    # Identity (both sides)
    for a in carrier:
        if op(identity, a) != a or op(a, identity) != a:
            return False
    # Inverses (for each a, some b with a*b = b*a = identity)
    for a in carrier:
        if not any(
            op(a, b) == identity and op(b, a) == identity
            for b in carrier
        ):
            return False
    return True


def demo():
    # (Z/5Z, +, 0) is a group
    Z5 = list(range(5))
    assert is_group(Z5, lambda x, y: (x + y) % 5, 0) is True

    # (Z/5Z, *, 1) is NOT a group: 0 has no multiplicative inverse
    assert is_group(Z5, lambda x, y: (x * y) % 5, 1) is False

    # But ((Z/5Z)*, *, 1) -- remove 0 -- IS a group (5 is prime)
    Z5star = [1, 2, 3, 4]
    assert is_group(Z5star, lambda x, y: (x * y) % 5, 1) is True

    # (Z/6Z, +, 0) is a group
    Z6 = list(range(6))
    assert is_group(Z6, lambda x, y: (x + y) % 6, 0) is True

    # (Z/6Z)* under multiplication is NOT a group (6 is composite):
    # even nonzero residues like 2, 3, 4 share factors with 6 and have no
    # multiplicative inverse.
    Z6star = [1, 2, 3, 4, 5]
    assert is_group(Z6star, lambda x, y: (x * y) % 6, 1) is False

    # Klein four-group V4: {e, a, b, c} where every non-identity element
    # has order 2 and a*b = c, b*c = a, a*c = b. Table:
    #       e a b c
    #   e | e a b c
    #   a | a e c b
    #   b | b c e a
    #   c | c b a e
    table = {
        ("e", "e"): "e", ("e", "a"): "a", ("e", "b"): "b", ("e", "c"): "c",
        ("a", "e"): "a", ("a", "a"): "e", ("a", "b"): "c", ("a", "c"): "b",
        ("b", "e"): "b", ("b", "a"): "c", ("b", "b"): "e", ("b", "c"): "a",
        ("c", "e"): "c", ("c", "a"): "b", ("c", "b"): "a", ("c", "c"): "e",
    }
    V4 = ["e", "a", "b", "c"]
    assert is_group(V4, lambda x, y: table[(x, y)], "e") is True

    print("OK")


if __name__ == "__main__":
    demo()
