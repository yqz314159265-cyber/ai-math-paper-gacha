#!/usr/bin/env python3
"""Check a Lucas primality DAG and enumerate the specified Fibonacci residue sieve.

Only the Python standard library is used. The Lucas conditions checked here are

    a^(n-1) = 1 (mod n), and a^((n-1)/q) != 1 (mod n)

for every prime q in the complete factorization of n-1. Together with recursively
checked primality of those q, Lucas' theorem proves n prime.
"""
from __future__ import annotations
import json
import math
import sys
from pathlib import Path

DEFAULT_DAG = Path(__file__).with_name("FibLucasDAG.json")
SMALL_FACTOR_CUTOFF = 10_000
LOW_INDEX = 137
HIGH_INDEX = 1_000


def trial_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def fib_list(limit: int) -> list[int]:
    out = [0, 1]
    for _ in range(2, limit + 1):
        out.append(out[-1] + out[-2])
    return out


def check_dag(data: dict) -> tuple[dict[int, dict], int]:
    assert data["schema"] == "lucas-primality-dag-v1"
    checked: dict[int, dict] = {}
    for row in data["nodesTopological"]:
        n = int(row["n"])
        a = int(row["base"])
        factors = [int(q) for q in row["factors"]]
        assert n > 2 and a > 1
        assert math.prod(factors) == n - 1, f"wrong factor product for {n}"
        for q in factors:
            if q <= SMALL_FACTOR_CUTOFF:
                assert trial_prime(q), f"composite leaf {q} in factorization of {n}"
            else:
                assert q in checked, f"factor {q} missing or ordered after {n}"
        assert pow(a, n - 1, n) == 1, f"Fermat condition failed for {n}"
        for q in set(factors):
            assert (n - 1) % q == 0
            assert pow(a, (n - 1) // q, n) != 1, f"Lucas condition failed for {n}, q={q}"
        checked[n] = row

    fibs = fib_list(HIGH_INDEX)
    for target in data["targets"]:
        i = int(target["index"])
        n = int(target["n"])
        assert fibs[i] == n, f"F_{i} does not match target"
        assert n in checked, f"target F_{i} has no Lucas node"
        assert checked[n]["base"] == target["base"]
        assert checked[n]["factors"] == target["factors"]
    return checked, len(data["nodesTopological"])


def check_half_orders(data: dict, fibs: list[int]) -> None:
    """Construct the order-d witness from a fully checked Lucas witness."""
    for target in data["targets"]:
        p, n, a = (int(target[key]) for key in ("index", "n", "base"))
        j = 2 * (p // 4)
        d = fibs[j] + fibs[j + 2]
        b, rem = divmod(n - 1, d)
        assert rem == 0 and b < d and d * d > n
        w = pow(a, b, n)
        assert pow(w, d, n) == 1
        residual = d
        primes = set(map(int, target["factors"]))
        local_checks = 0
        for q in sorted(primes):
            if residual % q:
                continue
            assert math.gcd(pow(w, d // q, n) - 1, n) == 1
            local_checks += 1
            while residual % q == 0:
                residual //= q
        assert residual == 1
        print(f"F_{p}: L_{j+1} has {len(str(d))} digits, {local_checks} prime-order checks pass.")


def check_cubic_orders(data: dict) -> None:
    """Choose a divisor crossing the cube-root threshold using large prime powers first."""
    for target in data["targets"]:
        p, n, a = (int(target[key]) for key in ("index", "n", "base"))
        factors = list(map(int, target["factors"]))
        powers = sorted(((q ** factors.count(q), q) for q in set(factors)), reverse=True)
        d = 1
        used = []
        for power, q in powers:
            d *= power
            used.append(q)
            if d**3 > n:
                break
        c, rem = divmod(n - 1, d)
        assert rem == 0 and n < d**3
        w = pow(a, c, n)
        assert pow(w, d, n) == 1
        assert all(math.gcd(pow(w, d // q, n) - 1, n) == 1 for q in used)
        prod, total = divmod(c, d)
        disc = total * total - 4 * prod
        if n < d * d:
            test = "square-root bound"
        else:
            assert disc < 0 or math.isqrt(disc)**2 != disc
            test = "cubic discriminant"
        print(f"F_{p}: {test} with {len(used)} distinct prime factors of a {len(str(d))}-digit divisor.")


def enumerate_candidates(fibs: list[int]) -> list[int]:
    """Prime indices 137 < n <= 1000 passing 2^(F_n) == 2 mod F_n."""
    out = []
    for n in range(LOW_INDEX + 1, HIGH_INDEX + 1):
        if trial_prime(n) and pow(2, fibs[n], fibs[n]) == 2 % fibs[n]:
            out.append(n)
    return out


def main() -> None:
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_DAG
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    checked, node_count = check_dag(data)
    fibs = fib_list(HIGH_INDEX)
    check_half_orders(data, fibs)
    check_cubic_orders(data)
    candidates = enumerate_candidates(fibs)
    targets = sorted(int(t["index"]) for t in data["targets"])
    assert targets == [359, 431, 433, 449, 509, 569, 571]
    assert candidates == targets, f"unexpected candidates: {candidates}"
    print(f"DAG: {node_count} Lucas nodes verified; all factor products and residues pass.")
    print(f"Fibonacci target values: {len(targets)} exact index/value checks pass.")
    print(f"Residue sieve (137 < n <= 1000): {candidates}")
    print("All seven candidates have recursively checked Lucas certificates.")


if __name__ == "__main__":
    main()
