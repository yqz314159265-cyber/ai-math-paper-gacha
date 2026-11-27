"""Generate reproducible, standard-library Lucas data for F_131 and F_137."""

from math import prod


def fib(n: int) -> int:
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def factorint_trial(n: int) -> dict[int, int]:
    """Exact trial division; these two p-1 values have modest prime factors."""
    factors: dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


for index in (131, 137):
    p = fib(index)
    factors = factorint_trial(p - 1)
    assert p - 1 == prod(q**e for q, e in factors.items())
    witness = next(
        a for a in range(2, 100)
        if pow(a, p - 1, p) == 1
        and all(pow(a, (p - 1) // q, p) != 1 for q in factors)
    )
    print(f"F_{index} = {p}")
    print("factors(F_n - 1) =", factors)
    print("Lucas witness =", witness)
    print("residues =", {
        q: pow(witness, (p - 1) // q, p) for q in factors
    })
