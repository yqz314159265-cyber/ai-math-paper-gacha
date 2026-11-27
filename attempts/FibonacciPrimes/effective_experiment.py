"""Check the constructive sieve at the first prime congruent to one modulo lcm(1,...,K+1)."""
import json
from math import lcm
from pathlib import Path

from experiment import is_prime_u64
from linear_experiment import fib_mod


def main():
    rows = []
    for k in range(4, 36):
        modulus = lcm(*range(1, k + 2))
        p = modulus + 1
        while not is_prime_u64(p):
            p += modulus
        candidates = [j*p + sign for j in range(1, k + 1) for sign in (-1, 1)
                      if j*p + sign <= k*p]
        for d in candidates:
            if fib_mod(p, d) == 0:
                raise ValueError(f"candidate {d} divides F_{p} for K={k}")
        rows.append({"K": k, "modulus": modulus, "first_prime_in_class": p,
                     "excluded_through": k*p, "linear_candidates_checked": len(candidates)})
    result = json.dumps(rows, indent=2) + "\n"
    Path(__file__).with_name("effective_results.json").write_text(result, encoding="utf-8")
    print(result, end="")


if __name__ == "__main__":
    main()
