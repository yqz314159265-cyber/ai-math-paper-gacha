"""Search verified factors of F_p - 1 for rank-assisted order certificates."""
import json
import math
import random
from collections import Counter
from pathlib import Path

from check_fib_lucas import check_dag

DIRECTORY = Path(__file__).parent


def candidate_orders(powers, random_source, n, exponent):
    """Sample prefix products below the classical square or cube threshold."""
    for _ in range(1_000):
        random_source.shuffle(powers)
        d = 1
        factors = []
        for q, multiplicity in powers:
            d *= q**multiplicity
            factors.extend([q]*multiplicity)
            if d**exponent >= n:
                break
            yield d, factors.copy()


def make_witness(n, a, d, factors):
    c, remainder = divmod(n-1, d)
    assert remainder == 0 and math.prod(factors) == d
    w = pow(a, c, n)
    assert pow(w, d, n) == 1
    assert all(math.gcd(pow(w, d//q, n)-1, n) == 1 for q in set(factors))
    return w


def main():
    data = json.loads((DIRECTORY/"FibLucasDAG.json").read_text(encoding="utf8"))
    check_dag(data)
    rng = random.Random(2971)
    square_examples = []
    cube_examples = []
    for target in data["targets"]:
        p, n, a = (int(target[key]) for key in ("index", "n", "base"))
        counts = Counter(map(int, target["factors"]))
        powers = [(q, e) for q, e in counts.items() if q != p]
        inert = n%p == p-1
        assert inert == (p%5 in (2, 3))

        best = None
        for d, factors in candidate_orders(powers, rng, n, 2):
            j = (-2*pow(d, -1, p))%p
            square_bound = (d*j+1)**2
            opposite_bound = (d*p+1)*(d*j+1)
            if n >= square_bound and (not inert or n >= opposite_bound):
                continue
            needs_opposite = n >= square_bound
            score = (not needs_opposite, d)
            if best is None or score < best[0]:
                best = score, dict(p=p, d=d, j=j, qs=factors, inert=inert,
                                   needsOpposite=needs_opposite, n=n)
        assert best is not None
        item = best[1]
        item["w"] = make_witness(n, a, item["d"], item["qs"])
        square_examples.append(item)
        print(f"F_{p}: j={item['j']}, floor(sqrt(F_p)/d)={math.isqrt(n)//item['d']}.")

        if not inert:
            continue
        best_cube = None
        for d, factors in candidate_orders(powers, rng, n, 3):
            j = (-2*pow(d, -1, p))%p
            if n+d*d*j*j >= 1+d*d*p+d**3*p*j:
                continue
            c = (n-1)//d
            product, total = divmod(c, d*p)
            delta = total*total - 4*p*product
            if delta >= 0 and math.isqrt(delta)**2 == delta:
                continue
            if best_cube is None or d < best_cube["d"]:
                best_cube = dict(p=p, n=n, d=d, j=j, c=c, qs=factors, delta=delta)
        assert best_cube is not None
        best_cube["w"] = make_witness(n, a, best_cube["d"], best_cube["qs"])
        cube_examples.append(best_cube)
        print(f"F_{p}: cubic j={best_cube['j']}, floor(F_p/d³)={n//best_cube['d']**3}.")

    result = {"square": square_examples, "cubic": cube_examples}
    (DIRECTORY/"rank_order_results.json").write_text(json.dumps(result, indent=2)+"\n", encoding="utf8")


if __name__ == "__main__":
    main()
