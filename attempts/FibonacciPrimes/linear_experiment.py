"""Explore the two allowed factor progressions at prime indices; Python standard library."""
import json
from math import isqrt
from pathlib import Path


def primes_through(limit):
    flags = bytearray([1]) * (limit + 1)
    flags[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if flags[p]:
            start = p*p
            flags[start::p] = bytes((limit-start)//p + 1)
    return flags


def fib_mod(index, modulus):
    a, b = 0, 1
    for digit in bin(index)[2:]:
        even = a * (2*b-a) % modulus
        odd = (a*a+b*b) % modulus
        a, b = (odd, (even+odd) % modulus) if digit == "1" else (even, odd)
    return a


def main():
    # Find the first admissible index up to this experimental search ceiling.
    bound = 250_000
    cutoffs = (1, 2, 4, 8, 16, 32, 64)
    prime = primes_through(max(cutoffs)*bound + 1)
    first = {}
    for p in range(7, bound+1, 2):
        if not prime[p]:
            continue
        for k in cutoffs:
            if k not in first and all(not prime[j*p-1] and not prime[j*p+1]
                                      for j in range(1, k+1)):
                first[k] = p
        if len(first) == len(cutoffs):
            break
    if len(first) != len(cutoffs):
        raise ValueError("search ceiling reached before every cutoff was witnessed")

    least_factors = []
    for p in (first[16], first[32]):
        # The rank theorem covers all prime divisors. Visit both progressions
        # in increasing order. Modular doubling avoids materializing F_p.
        for j in range(1, 501):
            hit = next((q for q in (j*p-1, j*p+1) if fib_mod(p, q) == 0), None)
            if hit is not None:
                least_factors.append({"index": p, "multiplier": j, "least_factor": hit})
                break
        else:
            raise ValueError(f"no witness found within the search limit at {p}")
    result = {"first_prime_index_above_five": first, "least_factors": least_factors}
    out = json.dumps(result, indent=2) + "\n"
    Path(__file__).with_name("linear_results.json").write_text(out, encoding="utf-8")
    print(out, end="")


if __name__ == "__main__":
    main()
