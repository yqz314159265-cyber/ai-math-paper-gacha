"""Replay the cubic certificate for F_2971 with Python's standard library."""
import json
import math
from pathlib import Path

from check_fib_lucas import SMALL_FACTOR_CUTOFF, check_nodes, fib_list, trial_prime


def main() -> None:
    data = json.loads(Path(__file__).with_name("fib2971_certificate.json").read_text(encoding="utf8"))
    nodes = check_nodes(data["nodes"])
    index = data["index"]
    n, d, c, w = (int(data[k]) for k in ("n", "d", "c", "w"))
    assert index == 2971 and fib_list(index)[index] == n
    factors = list(map(int, data["factors"]))
    for q in factors:
        assert q in nodes or (q <= SMALL_FACTOR_CUTOFF and trial_prime(q))
    assert math.prod(factors) == d and n == d*c + 1
    assert d*d < n < d**3
    assert w == pow(data["seed"], c, n) and pow(w, d, n) == 1
    assert all(math.gcd(pow(w, d//q, n) - 1, n) == 1 for q in set(factors))
    product, total = divmod(c, d)
    discriminant = total*total - 4*product
    assert discriminant == int(data["discriminant"])
    assert discriminant < 0 or math.isqrt(discriminant)**2 != discriminant
    print(f"F_{index} has {len(str(n))} digits. Verified {len(nodes)} recursive Lucas nodes.")
    print(f"Order d has {len(str(d))} digits and {len(set(factors))} distinct prime factors.")
    print("All order checks pass, d² < F_2971 < d³, and the discriminant is not a square.")


if __name__ == "__main__":
    main()
