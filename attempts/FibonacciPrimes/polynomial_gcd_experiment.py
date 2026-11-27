"""Check the degree of gcd(D_k + 3, X^q - X) without enumerating field elements."""
import json
from pathlib import Path

from linear_experiment import fib_mod, primes_through


def trim(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def remainder(dividend, divisor, q):
    """Polynomials use increasing coefficient order."""
    result = dividend.copy()
    inverse = pow(divisor[-1], -1, q)
    while len(result) >= len(divisor):
        offset = len(result) - len(divisor)
        scale = result[-1] * inverse % q
        for i, term in enumerate(divisor):
            result[i + offset] = (result[i + offset] - scale * term) % q
        trim(result)
    return result


def multiply_mod(a, b, modulus, q):
    if not a or not b:
        return []
    result = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            result[i + j] += ai * bj
    return remainder(trim([c % q for c in result]), modulus, q)


def dickson_shift(k):
    """Coefficients in Z of D_k(X,1)+3 for k≥1."""
    old, current = [2], [0, 1]
    for _ in range(1, k):
        nxt = [0] + current
        for i, c in enumerate(old):
            nxt[i] -= c
        old, current = current, nxt
    current[0] += 3
    return current


def frobenius_gcd_degree(shift, q):
    modulus = [c % q for c in shift]
    result = [1]
    x = [0, 1]
    for bit in bin(q)[2:]:
        result = multiply_mod(result, result, modulus, q)
        if bit == "1":
            result = multiply_mod(result, x, modulus, q)
    result += [0] * max(0, 2 - len(result))
    result[1] = (result[1] - 1) % q
    a, b = modulus, trim(result)
    while b:
        a, b = b, remainder(a, b, q)
    return len(a) - 1


def main():
    limit = 100_000
    prime = primes_through(limit + 1)
    counts = {}
    for k in (2, 4, 6, 8, 10, 12):
        shift = dickson_shift(k)
        tested = hits = 0
        for q in range(7, limit + 1, 2):
            if not prime[q]:
                continue
            t = q + 1 if q % 5 in (2, 3) else q - 1
            p, rem = divmod(t, k)
            if rem or p <= 5 or not prime[p]:
                continue
            degree = frobenius_gcd_degree(shift, q)
            divides = fib_mod(p, q) == 0
            if degree != (k if divides else 0):
                raise ValueError(f"degree={degree}, p={p}, q={q}, k={k}, divides={divides}")
            tested += 1
            hits += int(divides)
        counts[k] = {"tested": tested, "full_degree": hits, "degree_zero": tested - hits}
    payload = {"prime_q_upper_bound": limit, "prime_p_lower_bound_exclusive": 5, "by_k": counts}
    data = json.dumps(payload, indent=2) + "\n"
    Path(__file__).with_name("polynomial_gcd_results.json").write_text(data, encoding="utf-8")
    print(data, end="")


if __name__ == "__main__":
    main()
