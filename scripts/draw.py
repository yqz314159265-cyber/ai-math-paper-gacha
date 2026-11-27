"""One draw from the preselected, ordered shortlist. Pass the receipt to replay."""
import argparse
import json
import secrets

UPSTREAM = "ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8"
CANDIDATES = [
    ("Erdos287PrimePair", "Erdos287.erdos_287.variants.prime_conjecture",
     "FormalConjectures/ErdosProblems/287.lean"),
    ("Erdos1003", "Erdos1003.erdos_1003",
     "FormalConjectures/ErdosProblems/1003.lean"),
    ("FibonacciPrimes", "FibonacciPrimes.fib_primes_infinite",
     "FormalConjectures/Wikipedia/FibonacciPrimes.lean"),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", help="replay a hex string of accepted and rejected bytes")
    args = parser.parse_args()
    supplied = bytes.fromhex(args.receipt) if args.receipt is not None else None
    # Use rejection sampling so all three outcomes have exactly equal probability.
    ceiling = 256 - 256 % len(CANDIDATES)
    receipt = bytearray()
    while True:
        if supplied is None:
            value = secrets.token_bytes(1)[0]
        else:
            if len(receipt) >= len(supplied):
                parser.error("receipt ends before an accepted byte")
            value = supplied[len(receipt)]
        receipt.append(value)
        if value < ceiling:
            break
    if supplied is not None and len(receipt) != len(supplied):
        parser.error("unused bytes after selection")
    index = value % len(CANDIDATES)
    print(json.dumps(dict(upstream=UPSTREAM, candidates=CANDIDATES, receipt=receipt.hex(),
                          index=index, selected=CANDIDATES[index][0]), indent=2))


if __name__ == "__main__":
    main()
