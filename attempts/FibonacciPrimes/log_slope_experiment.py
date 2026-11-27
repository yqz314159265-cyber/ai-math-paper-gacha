"""Count and filter prime candidates q = k*p ± 1 for prime-index Fibonacci terms."""
import json
from math import isqrt
from pathlib import Path

LIMIT = 1_000_000
PREFIXES = (10_000, 100_000, LIMIT)
LABELS = ("half", "single", "double")
LAYERS = (
    ("raw_candidate_pairs", "raw_candidate_indices"),
    ("character_aligned_pairs", "character_aligned_indices"),
    ("mod4_filtered_pairs", "mod4_filtered_indices"),
)


def prime_table(limit):
    table = bytearray(b"\x01") * (limit + 1)
    table[:2] = bytes(2)
    for p in range(2, isqrt(limit) + 1):
        if table[p]:
            start = p*p
            table[start::p] = bytes((limit-start)//p + 1)
    return table


def fibonacci_mod(n, modulus):
    """Binary doubling for (F_n,F_{n+1}) modulo modulus."""
    a, b = 0, 1
    for bit in bin(n)[2:]:
        c = a*((2*b-a) % modulus) % modulus
        d = (a*a+b*b) % modulus
        a, b = (d, (c+d) % modulus) if bit == "1" else (c, d)
    return a


def candidate_is_character_aligned(q, sign):
    """Match the q−1 split branch or q+1 inert branch selected by (5/q)."""
    if sign == -1:  # q = k*p - 1, so p divides q+1.
        return q % 5 in (2, 3)
    return q % 5 in (1, 4)  # q = k*p + 1, so p divides q−1.


def sample(limit, prefixes):
    # q never exceeds 2*floor(log2(limit))*limit.
    table = prime_table(2*limit*(limit.bit_length()-1)+1)
    counts = {
        name: {
            "prime_pair_indices": 0,
            "factor_indices": 0,
            **{pair_key: 0 for pair_key, _ in LAYERS},
            **{index_key: 0 for _, index_key in LAYERS},
        }
        for name in LABELS
    }
    examples = []
    num_primes = 0
    snapshots = {}
    for p in range(6, limit+1):
        if table[p]:
            num_primes += 1
            binary_log = p.bit_length()-1
            cutoffs = (binary_log//2, binary_log, 2*binary_log)
            max_bound = cutoffs[-1]*p
            pairs = []
            least_factor = None

            # Track every prime pair through the largest cutoff. The old early
            # break hid later raw candidates once a factor had already appeared.
            for k in range(2, cutoffs[-1]+1, 2):
                for sign in (-1, 1):
                    q = k*p+sign
                    if q > max_bound or not table[q]:
                        continue
                    aligned = candidate_is_character_aligned(q, sign)
                    mod4_ok = aligned and q % 4 == 1
                    is_factor = fibonacci_mod(p, q) == 0
                    assert not is_factor or mod4_ok
                    pairs.append((q, aligned, mod4_ok, is_factor))
                    if is_factor and (least_factor is None or q < least_factor):
                        least_factor = q

            for name, cutoff in zip(LABELS, cutoffs):
                bound = cutoff*p
                in_bound = [row for row in pairs if row[0] <= bound]
                aligned = [row for row in in_bound if row[1]]
                mod4_filtered = [row for row in in_bound if row[2]]
                factor = any(row[3] for row in in_bound)
                counts[name]["raw_candidate_pairs"] += len(in_bound)
                counts[name]["raw_candidate_indices"] += bool(in_bound)
                counts[name]["character_aligned_pairs"] += len(aligned)
                counts[name]["character_aligned_indices"] += bool(aligned)
                counts[name]["mod4_filtered_pairs"] += len(mod4_filtered)
                counts[name]["mod4_filtered_indices"] += bool(mod4_filtered)
                # Keep the original column and its exact historical meaning.
                counts[name]["prime_pair_indices"] += bool(in_bound)
                counts[name]["factor_indices"] += factor
            if least_factor is not None and len(examples) < 12:
                examples.append({"index": p, "least_factor": least_factor})
        if p in prefixes:
            snapshots[p] = {
                "prime_indices_above_5": num_primes,
                "cutoffs": {name: values.copy() for name, values in counts.items()},
            }
    return {"prefixes": snapshots, "first_factor_examples": examples}


def check_small():
    """Cross-check factor-index totals by directly dividing the integer F_p."""
    nmax = 97
    a, b = 0, 1
    table = prime_table(nmax)
    expected = [0, 0, 0]
    for p in range(nmax+1):
        if p > 5 and table[p]:
            log2 = p.bit_length()-1
            for i, k in enumerate((log2//2, log2, 2*log2)):
                expected[i] += any(a % d == 0 for d in range(2, min(a, k*p)+1))
        a, b = b, a+b
    observed = sample(nmax, (nmax,))["prefixes"][nmax]["cutoffs"]
    assert [row["factor_indices"] for row in observed.values()] == expected


if __name__ == "__main__":
    check_small()
    results = sample(LIMIT, PREFIXES)
    output = Path(__file__).with_name("log_slope_results.json")
    output.write_text(json.dumps(results, indent=2)+"\n", encoding="utf8")
    print(json.dumps(results["prefixes"], indent=2))
