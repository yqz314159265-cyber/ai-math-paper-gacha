"""Final repository audit; supplements review of the Lean source and kernel checks."""

from __future__ import annotations

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECLARATION = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b"
)
AXIOM_BLOCK = re.compile(
    r"(?m)^\s*'([^']+)' depends on axioms:\s*\[(.*?)\]\s*$", re.S
)
NO_AXIOMS = re.compile(r"(?m)^\s*'([^']+)' does not depend on any axioms\s*$")
FORBIDDEN = {
    "sorry": re.compile(r"\bsorry\b"),
    "placeholder axiom": re.compile(r"\bsorryAx\b"),
    "native proof": re.compile(r"\bnative_decide\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom declaration": re.compile(r"\baxiom\b"),
    "unsafe declaration": re.compile(r"\bunsafe\b"),
    "implemented_by escape": re.compile(r"\bimplemented_by\b"),
}


def uncomment(source: str) -> str:
    """Remove Lean line/nested block comments and strings, preserving newlines."""
    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    while i < len(source):
        if block_depth:
            if source.startswith("/-", i):
                block_depth += 1
                out.extend("  ")
                i += 2
            elif source.startswith("-/", i):
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif in_string:
            if source[i] == "\\":
                out.extend("  ")
                i += min(2, len(source) - i)
            elif source[i] == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            block_depth = 1
            out.extend("  ")
            i += 2
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
        elif source[i] == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def lean_files(root: Path) -> list[Path]:
    paths = []
    for directory, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake"}]
        paths.extend(Path(directory) / name for name in files if name.endswith(".lean"))
    return sorted(paths)


def scan_placeholders(paths: list[Path], root: Path) -> list[str]:
    problems = []
    for path in paths:
        clean = uncomment(path.read_text(encoding="utf-8"))
        for label, pattern in FORBIDDEN.items():
            for match in pattern.finditer(clean):
                line = clean.count("\n", 0, match.start()) + 1
                problems.append(f"{path.relative_to(root)}:{line}: {label}")
    return problems


def attempt_theorems(attempts: Path) -> tuple[list[str], list[str]]:
    names: list[str] = []
    problems: list[str] = []
    for path in sorted(attempts.rglob("*.lean")):
        if not path.is_file() or ".lake" in path.parts:
            continue
        source = uncomment(path.read_text(encoding="utf-8"))
        found = [m.group(1) for line in source.splitlines()
                 if (m := DECLARATION.match(line))]
        if found and not re.search(r"(?m)^\s*namespace\s+MathGacha\b", source):
            problems.append(f"{path}: theorem/lemma file missing namespace MathGacha")
        names.extend("MathGacha." + name for name in found)
    duplicates = sorted({name for name in names if names.count(name) > 1})
    problems.extend(f"duplicate declaration: {name}" for name in duplicates)
    if not names:
        problems.append(f"no Lean modules found under {attempts}")
    return names, problems


def parse_axiom_output(output: str, expected: list[str]) -> list[str]:
    problems = []
    blocks = list(AXIOM_BLOCK.finditer(output))
    seen: dict[str, int] = {}
    for match in NO_AXIOMS.finditer(output):
        seen[match.group(1)] = seen.get(match.group(1), 0) + 1
    for block in blocks:
        name = block.group(1)
        seen[name] = seen.get(name, 0) + 1
        body = block.group(2).strip()
        axioms = [] if body == "no axioms" else [
            part.strip() for part in body.split(",") if part.strip()
        ]
        unknown = sorted(set(axioms) - ALLOWED_AXIOMS)
        if unknown:
            problems.append(f"{name}: disallowed/unknown axioms: {', '.join(unknown)}")
    for name in sorted(set(seen) - set(expected)):
        problems.append(f"unexpected axiom report for {name}")
    for name in expected:
        count = seen.get(name, 0)
        if count == 0:
            problems.append(f"missing axiom report for {name}")
        elif count > 1:
            problems.append(f"duplicate axiom report for {name}")
    # Any nonempty output line not belonging to Lean diagnostics or a recognized
    # report can signal a format change; fail closed instead of silently skipping it.
    residue = NO_AXIOMS.sub("", AXIOM_BLOCK.sub("", output))
    residue = re.sub(r"(?m)^\s*$", "", residue)
    if residue.strip():
        problems.append("unrecognized output from lake env lean: " + residue.strip()[:300])
    return problems


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    root = args.root.resolve()
    attempts = root / "attempts"
    if not attempts.is_dir():
        print(f"ERROR: missing {attempts}", file=sys.stderr)
        return 1

    names, problems = attempt_theorems(attempts)
    lean = lean_files(root)
    problems.extend(scan_placeholders(lean, root))
    if problems:
        print("ERROR: source audit failed", file=sys.stderr)
        print("\n".join(f"- {p}" for p in problems), file=sys.stderr)
        return 1

    build = subprocess.run(["lake", "build"], cwd=root, text=True,
                           encoding="utf-8", errors="replace",
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if build.returncode:
        print(build.stdout, file=sys.stderr)
        print("ERROR: lake build failed", file=sys.stderr)
        return build.returncode
    build_lines = [line for line in build.stdout.splitlines() if line.strip()]
    if build_lines:
        print("lake build final line: " + build_lines[-1])
    else:
        print("lake build final line: (no output; exit code 0)")

    with tempfile.TemporaryDirectory(prefix="math-gacha-audit-") as temp:
        probe = Path(temp) / "Audit.lean"
        probe.write_text("import Gacha\n\n" + "\n".join(
            f"#print axioms {name}" for name in names) + "\n", encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=root,
                                text=True, encoding="utf-8", errors="replace",
                                stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout, file=sys.stderr)
        print("ERROR: Lean axiom probe failed", file=sys.stderr)
        return result.returncode
    problems = parse_axiom_output(result.stdout, names)
    if problems:
        print("ERROR: axiom audit failed", file=sys.stderr)
        print("\n".join(f"- {p}" for p in problems), file=sys.stderr)
        return 1
    print("Raw #print axioms output:")
    print(result.stdout, end="" if result.stdout.endswith("\n") else "\n")
    print(f"Audit passed: lake build; {len(names)} theorem/lemma axiom reports; "
          f"{len(lean)} Lean files scanned.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
