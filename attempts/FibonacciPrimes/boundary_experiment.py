"""Check the exact 2p-1 factor criterion and its multiplicity for prime indices."""
import json
from pathlib import Path

from linear_experiment import fib_mod, primes_through


def main():
    bound = 1_000_000
    prime = primes_through(2 * bound)
    checked = pairs = divisors = repeated = 0
    by_residue = {}
    first = []
    for p in range(11, bound + 1, 2):
        if not prime[p]:
            continue
        checked += 1
        q = 2 * p - 1
        pair = bool(prime[q])
        divides = fib_mod(p, q) == 0
        if divides != (pair and p % 5 in (2, 4)):
            raise ArithmeticError(f"factor criterion failed at index {p}")
        if pair:
            pairs += 1
            entry = by_residue.setdefault(p % 5, {"prime_pairs": 0, "divisors": 0})
            entry["prime_pairs"] += 1
            entry["divisors"] += int(divides)
        if divides:
            divisors += 1
            if len(first) < 12:
                first.append(p)
            square = q * q
            in_term = fib_mod(p, square) == 0
            in_neighbors = any(fib_mod(t, square) == 0 for t in (q - 1, q + 1))
            if in_term != in_neighbors:
                raise ArithmeticError(f"multiplicity criterion failed at {p}, {q}")
            repeated += int(in_term)

    result = {"index_bound": bound, "prime_indices_above_7": checked, "prime_pairs": pairs,
              "boundary_divisors": divisors, "repeated_boundary_divisors": repeated,
              "first_divisor_indices": first, "by_index_mod_5": dict(sorted(by_residue.items()))}
    out = json.dumps(result, indent=2) + "\n"
    Path(__file__).with_name("boundary_results.json").write_text(out, encoding="utf-8")
    print(out, end="")


if __name__ == "__main__":
    main()
