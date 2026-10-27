#!/usr/bin/env python3
"""Local source preflight; not a Lean proof check or Palomar certificate."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / "directed-cycles-lean"
sys.path.insert(0, str(PROJECT / "scripts"))
from verify import strip_comments


def main():
    files = []
    for path in ROOT.rglob("*.lean"):
        if {".git", ".lake"}.intersection(path.relative_to(ROOT).parts):
            continue
        if path.is_symlink():
            raise ValueError(f"Lean symlink: {path.relative_to(ROOT)}")
        data = path.read_bytes()
        if len(data.splitlines()) > 10000:
            raise ValueError(f"Oversized Lean file: {path.relative_to(ROOT)}")
        code = strip_comments(data.decode("utf-8"))
        if path.name != "lakefile.lean" and not re.match(r"\s*module\b", code):
            raise ValueError(f"Missing module header: {path.relative_to(ROOT)}")
        if path.parent == PROJECT / "DirectedCycles" or path.name in {
            "DirectedCycles.lean", "Solution.lean"
        }:
            if re.search(r"\b(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe)\b", code):
                raise ValueError(f"Forbidden proof escape: {path.relative_to(ROOT)}")
            if re.search(r"\bimport\s+(?:all\s+)?Challenge\b", code):
                raise ValueError(f"Proof imports Challenge: {path.relative_to(ROOT)}")
        files.append(path)
    challenge = PROJECT / "Challenge.lean"
    data = challenge.read_bytes()
    code = strip_comments(data.decode("utf-8"))
    if len(data) > 100 * 1024 or len(data.splitlines()) > 1000:
        raise ValueError("Challenge exceeds Palomar's hard size limit")
    if len(re.findall(r"\bsorry\b", code)) != 1:
        raise ValueError("Expected exactly one statement-only Challenge placeholder")
    imports = re.findall(r"^public import (\S+)$", code, re.M)
    if not imports or any(not module.startswith("Mathlib.") for module in imports):
        raise ValueError("Unexpected direct Challenge import")
    print(f"Source layout passed: {len(files)} Lean files; Challenge is {len(data.splitlines())} lines.")
    print("One statement-only placeholder; none in proof sources. Kernel checks still required.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, UnicodeError, ValueError, RuntimeError) as error:
        print(f"Source preflight failed: {error}", file=sys.stderr)
        sys.exit(1)
