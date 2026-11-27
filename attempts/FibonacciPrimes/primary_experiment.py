"""Compare prime-power Dickson tests with fast doubling at every eligible prime pair."""
import json
from collections import Counter
from functools import lru_cache
from math import isqrt
from pathlib import Path

from linear_experiment import fib_mod, primes_through
from polynomial_gcd_experiment import dickson_shift, frobenius_gcd_degree


@lru_cache(None)
def primary_factors(k):
    factors = []
    remaining = k
    for r in range(2, isqrt(k) + 1):
        if remaining % r == 0:
            power = 1
            while remaining % r == 0:
                remaining //= r
                power *= r
            factors.append(power)
    if remaining > 1:
        factors.append(remaining)
    return tuple(sorted(factors))


def main():
    limit = 40_000
    largest_k = 100
    prime = primes_through(limit + 1)
    checked = dividends = split = tests = 0
    first_failures = Counter()
    examples = []
    for q in range(7, limit + 1, 2):
        if not prime[q]:
            continue
        t = q + 1 if q % 5 in (2, 3) else q - 1
        for k in range(2, largest_k + 1, 2):
            p, remainder = divmod(t, k)
            if remainder or p <= 5 or not prime[p]:
                continue
            parts = primary_factors(k)
            degrees = []
            for part in parts:
                degree = frobenius_gcd_degree(dickson_shift(part), q)
                if degree not in (0, part):
                    raise ArithmeticError((q, k, part, degree))
                tests += 1
                degrees.append(degree)
                if degree == 0:
                    first_failures[part] += 1
                    break
            matches = all(degrees)
            actual = fib_mod(p, q) == 0
            if actual != matches:
                raise ArithmeticError((p, q, k, parts, degrees))
            checked += 1
            dividends += int(actual)
            split += int(len(parts) > 1)
            if actual and len(parts) >= 3 and len(examples) < 8:
                examples.append(dict(p=p, q=q, k=k, degrees=degrees))
    result = dict(prime_q_max=limit, multiplier_max=largest_k, eligible_pairs=checked,
                  divisibility_hits=dividends, multiple_primary_components=split,
                  polynomial_tests=tests, first_failed_degree=dict(sorted(first_failures.items())),
                  examples=examples)
    Path(__file__).with_name("primary_results.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(checked, dividends, split, tests)


if __name__ == "__main__":
    main()
