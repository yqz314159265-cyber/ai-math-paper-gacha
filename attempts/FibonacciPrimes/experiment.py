"""Exact 64-bit tests and a trial-factor sieve for prime-index Fibonacci terms."""
import json
from math import isqrt
from pathlib import Path
import re

# Sorenson & Webster, Math. Comp. 86 (2017), doi:10.1090/mcom/3134.
# The least strong pseudoprime to these twelve bases exceeds 2**64.
BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
EXACT_LIMIT = 93
INDEX_LIMIT = 10_000
FACTOR_LIMIT = 10_000


def is_prime_u64(n):
    if not 0 <= n < 2**64:
        raise ValueError("outside the exact test range")
    if n < 2:
        return False
    for p in BASES:
        if n % p == 0:
            return n == p
    d = n - 1
    s = 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in BASES:
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def primes_through(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            for multiple in range(p * p, limit + 1, p):
                flags[multiple] = 0
    return [n for n, flag in enumerate(flags) if flag]


def check_screen(candidates, primes, witnesses):
    # Second computation uses only residues, with no large Fibonacci integers.
    first_factor = {}
    for q in primes:
        a, b = 0, 1
        for n in range(1, INDEX_LIMIT + 1):
            a, b = b, (a + b) % q
            if a == 0 and n in candidates:
                first_factor.setdefault(n, q)
    actual = [(row["n"], row["least_prime_factor"]) for row in witnesses]
    if sorted(first_factor.items()) != actual:
        raise ValueError("modular recurrence disagrees with integer trial division")

    # Check the exact list used by the kernel proof against the experiment.
    source = (Path(__file__).parent / "Gacha" / "Screen.lean").read_text(encoding="utf-8")
    table = source.split("def screenWitnesses", 1)[1].split("theorem", 1)[0]
    pairs = [(int(n), int(q)) for n, q in re.findall(r"\((\d+), (\d+)\)", table)]
    if pairs != actual:
        raise ValueError("Lean witness table differs from the recomputed screen")


def main():
    primes = primes_through(max(INDEX_LIMIT, FACTOR_LIMIT))
    candidates = {p for p in primes if EXACT_LIMIT < p <= INDEX_LIMIT}
    factors = [q for q in primes if q <= FACTOR_LIMIT]
    exact = []
    eliminated = []
    survivors = []
    a, b = 0, 1
    for n in range(INDEX_LIMIT + 1):
        if n <= EXACT_LIMIT:
            exact.append({"n": n, "F_n": str(a), "prime": is_prime_u64(a)})
        elif n in candidates:
            divisor = next((q for q in factors if a % q == 0), None)
            if divisor is None:
                survivors.append(n)
            else:
                assert 1 < divisor < a and divisor % 4 == 1
                eliminated.append({"n": n, "least_prime_factor": divisor})
        a, b = b, a + b
    check_screen(candidates, factors, eliminated)
    result = {
        "exact_range": [0, EXACT_LIMIT],
        "prime_indices": [row["n"] for row in exact if row["prime"]],
        "rows": exact,
        "screen": {
            "prime_index_range": [EXACT_LIMIT + 1, INDEX_LIMIT],
            "trial_prime_bound": FACTOR_LIMIT,
            "tested": len(candidates),
            "composite_with_witness": eliminated,
            "survivors_without_a_factor_at_or_below_bound": survivors,
        },
    }
    Path(__file__).with_name("results.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print("Exact prime indices:", result["prime_indices"])
    print(f"Screen: {len(candidates)} tested, {len(eliminated)} composite, "
          f"{len(survivors)} without a factor ≤ {FACTOR_LIMIT}.")


if __name__ == "__main__":
    main()
