"""Search both possible progressions for divisors of Fibonacci numbers at large prime indices."""
import json
from pathlib import Path

from linear_experiment import fib_mod, primes_through


def find_divisors(p, limit, small_primes):
    """All divisors in this interval are prime by the lower bound on their prime factors."""
    if limit*p + 1 >= (2*p-1)**2:
        raise ValueError("linear range exceeds the proven primality cutoff")
    hits = []
    tested = 0
    for sign in (-1, 1):
        alive = bytearray([1]) * (limit + 1)
        for r in small_primes:
            if p % r == 0:
                continue
            first = (-sign * pow(p, -1, r)) % r or r
            if first <= limit:
                alive[first::r] = bytes((limit-first)//r + 1)
        for j in range(1, limit + 1):
            if not alive[j]:
                continue
            q = j*p + sign
            if q % 4 != 1 or (q % 5 in (2, 3)) != (sign == -1):
                continue
            tested += 1
            if fib_mod(p, q) == 0:
                hits.append(dict(j=j, sign=sign, divisor=q))
    return {"p": p, "tested_by_modular_doubling": tested,
            "divisors": sorted(hits, key=lambda record: record["divisor"])}


def main():
    limit = 3_000_000
    small_bound = 2_000
    directory = Path(__file__).parent
    rows = json.loads((directory / "effective_results.json").read_text(encoding="utf-8"))
    targets = sorted({r["first_prime_in_class"] for r in rows if r["first_prime_in_class"] > 1_000_000})
    flags = primes_through(small_bound)
    small = [r for r, prime in enumerate(flags) if prime]
    if min(targets) - 1 <= small_bound:
        raise ValueError("small-prime presieve would discard a possible target")
    result = [find_divisors(p, limit, small) for p in targets]
    payload = {"largest_multiplier": limit, "presieve_limit": small_bound, "results": result}
    (directory / "large_factor_results.json").write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    for row in result:
        print(row["p"], [hit["divisor"] for hit in row["divisors"]])


if __name__ == "__main__":
    main()
