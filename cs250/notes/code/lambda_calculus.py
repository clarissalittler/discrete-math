"""
Intermezzo — The Lambda Calculus
Runnable Python companion to CS 250's lambda-calculus intermezzo.

Contains:
- Church encodings of booleans (TRUE, FALSE, AND, OR, NOT, IF)
- Church encodings of naturals (ZERO, SUCC, PLUS, MULT, IS_ZERO)
- Decoders back to Python primitives so the assertions make sense.

Everything here is pure lambda calculus: no Python primitives except
for function abstraction and application. Nothing is recursive at the
lambda-calculus level; the recursion comes from unfolding the encoded
natural at the end.
"""


# --- Church booleans ---
# TRUE picks its first argument, FALSE picks its second.
TRUE = lambda t: lambda f: t
FALSE = lambda t: lambda f: f


def AND(p):
    return lambda q: p(q)(p)


def OR(p):
    return lambda q: p(p)(q)


def NOT(p):
    return p(FALSE)(TRUE)


def IF(p):
    return lambda t: lambda f: p(t)(f)


def unchurch_bool(b):
    """Decode a Church boolean to a Python bool."""
    return b(True)(False)


# --- Church naturals ---
# A Church numeral n takes a function f and a value x and applies f to x
# exactly n times. ZERO applies f zero times; THREE applies f three times.
ZERO = lambda f: lambda x: x
ONE = lambda f: lambda x: f(x)
TWO = lambda f: lambda x: f(f(x))
THREE = lambda f: lambda x: f(f(f(x)))


def SUCC(n):
    """Successor: apply f one more time than n does."""
    return lambda f: lambda x: f(n(f)(x))


def PLUS(m):
    """Addition: m applications of SUCC starting from n."""
    return lambda n: lambda f: lambda x: m(f)(n(f)(x))


def MULT(m):
    """Multiplication: m applications of (PLUS n) starting from ZERO."""
    return lambda n: lambda f: m(n(f))


def IS_ZERO(n):
    """Returns TRUE iff n is the Church encoding of zero.

    Trick: IS_ZERO applies n to the constant function (returns FALSE)
    starting from TRUE. If n is zero the starting value TRUE is returned;
    otherwise at least one application of the constant FALSE occurs.
    """
    return n(lambda _: FALSE)(TRUE)


def unchurch_nat(n):
    """Decode a Church numeral to a Python int by applying it to (+1) and 0."""
    return n(lambda x: x + 1)(0)


def demo():
    # Church booleans
    assert unchurch_bool(TRUE) is True
    assert unchurch_bool(FALSE) is False

    assert unchurch_bool(AND(TRUE)(TRUE)) is True
    assert unchurch_bool(AND(TRUE)(FALSE)) is False
    assert unchurch_bool(AND(FALSE)(TRUE)) is False
    assert unchurch_bool(AND(FALSE)(FALSE)) is False

    assert unchurch_bool(OR(TRUE)(FALSE)) is True
    assert unchurch_bool(OR(FALSE)(FALSE)) is False

    assert unchurch_bool(NOT(TRUE)) is False
    assert unchurch_bool(NOT(NOT(TRUE))) is True

    # IF branch
    assert IF(TRUE)("yes")("no") == "yes"
    assert IF(FALSE)("yes")("no") == "no"

    # Church naturals
    assert unchurch_nat(ZERO) == 0
    assert unchurch_nat(ONE) == 1
    assert unchurch_nat(TWO) == 2
    assert unchurch_nat(THREE) == 3

    # SUCC increments
    assert unchurch_nat(SUCC(ZERO)) == 1
    assert unchurch_nat(SUCC(SUCC(SUCC(ZERO)))) == 3

    # PLUS: 2 + 3 = 5
    FIVE = PLUS(TWO)(THREE)
    assert unchurch_nat(FIVE) == 5

    # MULT: 2 * 3 = 6
    SIX = MULT(TWO)(THREE)
    assert unchurch_nat(SIX) == 6

    # IS_ZERO
    assert unchurch_bool(IS_ZERO(ZERO)) is True
    assert unchurch_bool(IS_ZERO(ONE)) is False
    assert unchurch_bool(IS_ZERO(SIX)) is False

    # Church numerals and booleans together: if 0 then 42 else 99
    def unchurch_into(n, t, f):
        return IF(IS_ZERO(n))(t)(f)

    assert unchurch_into(ZERO, 42, 99) == 42
    assert unchurch_into(TWO, 42, 99) == 99

    print("OK")


if __name__ == "__main__":
    demo()
