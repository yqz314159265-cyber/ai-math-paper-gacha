"""Compare the third possible divisor with a cubic over F_q and Sun's quadratic form."""
import json
from math import isqrt
from pathlib import Path

from linear_experiment import fib_mod, primes_through
from polynomial_gcd_experiment import frobenius_gcd_degree


def sun_representation(q):
    """Find q = 5 x² + 108 y² over nonnegative integers, if possible."""
    for y in range(isqrt(q // 108) + 1):
        square, remainder = divmod(q - 108 * y * y, 5)
        if remainder == 0 and isqrt(square) ** 2 == square:
            return [isqrt(square), y]
    return None


def main():
    limit = 1_000_000
    primes = primes_through(6 * limit)
    count = eligible = divides = 0
    examples = []
    degrees = {}
    for p in range(7, limit + 1, 2):
        if not primes[p]:
            continue
        count += 1
        q = 6*p - 1
        actual = fib_mod(p, q) == 0
        represented = bool(primes[q]) and sun_representation(q) is not None
        cubic = False
        if primes[q] and p % 5 in (3, 4):
            eligible += 1
            degree = frobenius_gcd_degree([-1, 3, 0, 1], q)
            degrees[degree] = degrees.get(degree, 0) + 1
            cubic = degree > 0
        if actual != cubic or actual != represented:
            raise ArithmeticError((p, q, actual, cubic, represented))
        if actual:
            divides += 1
            if len(examples) < 12:
                roots = [x for x in range(q) if (x**3 + 3*x - 1) % q == 0]
                examples.append(dict(p=p, q=q, roots=roots, form=sun_representation(q)))
    result = dict(prime_index_limit=limit, prime_indices=count,
                  eligible_by_prime_and_residue=eligible, root_counts=degrees,
                  divides=divides, first_examples=examples)
    content = json.dumps(result, indent=2) + "\n"
    Path(__file__).with_name("six_results.json").write_text(content, encoding="utf-8")
    print(count, eligible, divides, degrees)


if __name__ == "__main__":
    main()
