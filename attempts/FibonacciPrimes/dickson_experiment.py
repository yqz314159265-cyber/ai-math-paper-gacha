"""Compare finite-field Dickson roots with independently computed Fibonacci residues."""
import json
from pathlib import Path

from linear_experiment import fib_mod, primes_through


def dickson_value(k, z, q):
    """Compute D_k(z) with D_0=2, D_1=z, D_{n+2}=zD_{n+1}-D_n."""
    a, b = 2, z
    for bit in bin(k)[2:]:
        middle = (a * b - z) % q
        if bit == "0":
            a, b = (a * a - 2) % q, middle
        else:
            a, b = middle, (b * b - 2) % q
    return a


def main():
    bound = 5000
    prime = primes_through(bound + 1)
    totals = {"split": {"tested": 0, "divides": 0}, "nonsplit": {"tested": 0, "divides": 0}}
    splits = {}
    examples = []
    for q in range(7, bound + 1, 2):
        if not prime[q]:
            continue
        split = q % 5 in (1, 4)
        t = q - 1 if split else q + 1
        for p in range(7, t + 1, 2):
            if t % p or not prime[p]:
                continue
            k = t // p
            roots = [z for z in range(q) if dickson_value(k, z, q) == q - 3]
            divides = fib_mod(p, q) == 0
            if bool(roots) != divides:
                raise ValueError(f"root criterion disagrees for p={p}, q={q}, k={k}")
            data = totals["split" if split else "nonsplit"]
            data["tested"] += 1
            data["divides"] += int(divides)
            if roots:
                key = "all_k" if len(roots) == k else "between_one_and_k"
                splits[key] = splits.get(key, 0) + 1
                if len(examples) < 8:
                    examples.append({"p": p, "q": q, "k": k, "roots": roots})

    result = {"prime_factor_bound": bound, "index_condition": "prime p > 5 dividing q - (5/q)",
              "cases": totals, "positive_case_root_counts": splits, "first_positive_cases": examples}
    out = json.dumps(result, indent=2) + "\n"
    Path(__file__).with_name("dickson_results.json").write_text(out, encoding="utf-8")
    print(out, end="")


if __name__ == "__main__":
    main()
