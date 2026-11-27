"""Compare the local proposition with the declaration in the pinned upstream commit."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

from draw import CANDIDATES, UPSTREAM


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path, help="a clone of formal-conjectures")
    parser.add_argument("attempt", type=Path, help="attempts/<selected ID>")
    args = parser.parse_args()
    draw = json.loads((args.attempt / "draw.json").read_text(encoding="utf-8"))
    replay = subprocess.check_output(
        [sys.executable, str(Path(__file__).with_name("draw.py")), "--receipt", draw["receipt"]],
        encoding="utf-8")
    if json.loads(replay) != draw:
        raise SystemExit("receipt does not reproduce the recorded draw")
    card, qualified, path = CANDIDATES[draw["index"]]
    if (draw["upstream"], draw["selected"], args.attempt.name) != (UPSTREAM, card, card):
        raise SystemExit("draw metadata mismatch")
    source = subprocess.check_output(
        ["git", "-C", str(args.upstream), "show", f"{UPSTREAM}:{path}"], encoding="utf-8")
    namespace, _, decl = qualified.partition(".")
    if f"namespace {namespace}" not in source:
        raise SystemExit("upstream namespace missing")
    target = re.search(rf"^theorem {re.escape(decl)}\s*:\s*(.*?)\s*:= by", source, re.M | re.S)
    local = (args.attempt / "Gacha" / "Statement.lean").read_text(encoding="utf-8")
    copied = re.search(r"^def Original : Prop :=\s*(.*?)\s*\nend MathGacha", local, re.M | re.S)
    if target is None or copied is None or target[1].split() != copied[1].split():
        raise SystemExit("proposition mismatch")
    print(f"Statement matches {UPSTREAM}:{path} ({qualified}).")


if __name__ == "__main__":
    main()
