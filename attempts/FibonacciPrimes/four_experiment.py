"""Check the q = 4p + 1 Fibonacci divisibility criterion for prime p ≤ 10^6.

Uses the exact sieve and fast-doubling fib_mod helper from linear_experiment.py.
Only Python's standard library is needed.
"""

import json
from collections import defaultdict
from math import isqrt
from pathlib import Path

from linear_experiment import fib_mod, primes_through


LIMIT = 1_000_000


def sqrt5_mod_prime_5mod8(q: int) -> int:
    """Square root of 5 mod prime q ≡ 5 (mod 8), using the 5-mod-8 formula."""
    root = pow(5, (q + 3) // 8, q)
    if root * root % q != 5:
        root = root * pow(2, (q - 1) // 4, q) % q
    assert root * root % q == 5
    return root


def legendre_nonzero(a: int, q: int) -> bool:
    """Return whether nonzero a is a quadratic nonresidue modulo prime q."""
    symbol = pow(a % q, (q - 1) // 2, q)
    assert symbol in (1, q - 1)
    return symbol == q - 1


def main() -> None:
    prime = primes_through(4 * LIMIT + 1)
    groups = defaultdict(lambda: {
        "prime_indices": 0,
        "q_prime": 0,
        "q_composite": 0,
        "q_divides_Fp": 0,
        "q_prime_divides_Fp": 0,
        "q_composite_divides_Fp": 0,
        "criterion_checked": 0,
        "criterion_matches": 0,
        "both_root_signs_agree": 0,
        "single_power_checked": 0,
        "quadratic_form_checked": 0,
        "quadratic_form_matches": 0,
    })
    hits = []
    simultaneous = []
    composite_hits = []
    mismatches = []
    sign_disagreements = []

    for p in range(7, LIMIT + 1, 2):
        if not prime[p]:
            continue
        r = p % 5
        stat = groups[r]
        stat["prime_indices"] += 1
        q = 4 * p + 1
        q_is_prime = bool(prime[q])
        divides = fib_mod(p, q) == 0
        stat["q_prime" if q_is_prime else "q_composite"] += 1
        if divides:
            stat["q_divides_Fp"] += 1
            if q_is_prime:
                stat["q_prime_divides_Fp"] += 1
            else:
                stat["q_composite_divides_Fp"] += 1
                composite_hits.append({"p": p, "q": q})

        other = 2 * p - 1
        other_divides = fib_mod(p, other) == 0
        if divides and other_divides:
            simultaneous.append({
                "p": p,
                "q": q,
                "q_prime": q_is_prime,
                "2p_minus_1": other,
                "2p_minus_1_prime": bool(prime[other]),
            })

        criterion = None
        roots_agree = None
        if q_is_prime and r == 2:
            # Here q ≡ 4 (mod 5) and q ≡ 5 (mod 8), so sqrt(5) exists.
            assert q % 5 == 4 and q % 8 == 5
            if (pow(5, p, q) == 1) != divides:
                raise ValueError(f"base-five power test disagrees at p={p}, q={q}")
            stat["single_power_checked"] += 1
            represented = any(
                isqrt(q - 100*y*y)**2 == q - 100*y*y
                for y in range(isqrt(q // 100) + 1)
            )
            stat["quadratic_form_checked"] += 1
            if represented != divides:
                raise ValueError(f"quadratic form disagrees at p={p}, q={q}")
            stat["quadratic_form_matches"] += 1
            s = sqrt5_mod_prime_5mod8(q)
            inv2 = (q + 1) // 2
            a_plus = (1 + s) * inv2 % q
            a_minus = (1 - s) * inv2 % q
            plus_nonsquare = legendre_nonzero(a_plus, q)
            minus_nonsquare = legendre_nonzero(a_minus, q)
            roots_agree = plus_nonsquare == minus_nonsquare
            criterion = plus_nonsquare
            stat["criterion_checked"] += 1
            if roots_agree:
                stat["both_root_signs_agree"] += 1
            else:
                sign_disagreements.append({"p": p, "q": q, "s": s})
            if divides == criterion:
                stat["criterion_matches"] += 1
            else:
                mismatches.append({
                    "p": p,
                    "q": q,
                    "q_divides_Fp": divides,
                    "a_is_nonsquare": criterion,
                    "a_plus": a_plus,
                    "a_minus": a_minus,
                })

        if divides and len(hits) < 10:
            hits.append({
                "p": p,
                "p_mod_5": r,
                "q": q,
                "q_prime": q_is_prime,
                "q_divides_Fp": divides,
                "2p_minus_1": other,
                "2p_minus_1_prime": bool(prime[other]),
                "2p_minus_1_divides_Fp": other_divides,
                "criterion_a_nonsquare": criterion,
                "both_root_signs_agree": roots_agree,
            })

    assert not mismatches, f"quadratic criterion mismatches: {mismatches[:5]}"
    assert not sign_disagreements, f"root sign disagreements: {sign_disagreements[:5]}"

    result = {
        "search": {
            "prime_indices": "7 ≤ p ≤ 1,000,000",
            "q": "4p + 1",
            "criterion": "for q prime and p mod 5 = 2: q | F_p iff a=(1+sqrt(5))/2 is a quadratic nonresidue mod q",
            "single_power": "5^p = 1 mod q (q prime, p mod 5 = 2)",
            "quadratic_form": "q = x^2 + 100*y^2 (q prime, p mod 5 = 2)",
            "implementation": "standard-library sieve and fast-doubling fib_mod imported from linear_experiment.py",
        },
        "by_p_mod_5": {str(k): groups[k] for k in sorted(groups)},
        "q_divides_Fp_total": sum(x["q_divides_Fp"] for x in groups.values()),
        "first_10_q_divides_Fp": hits,
        "both_4p_plus_1_and_2p_minus_1_divide_Fp_total": len(simultaneous),
        "first_10_simultaneous": simultaneous[:10],
        "composite_q_divides_Fp_total": len(composite_hits),
        "first_10_composite_q_hits": composite_hits[:10],
        "quadratic_criterion_mismatches": mismatches,
        "root_sign_disagreements": sign_disagreements,
    }
    output = json.dumps(result, indent=2) + "\n"
    out_path = Path(__file__).with_name("four_experiment_results.json")
    out_path.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
