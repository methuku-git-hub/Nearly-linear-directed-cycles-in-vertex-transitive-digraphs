#!/usr/bin/env python3
"""Run the original verification in a new copy, preserving the published snapshot."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from check_snapshot import ROOT, check


def main():
    if "--help" in sys.argv:
        print(__doc__)
        print("Usage: python3 scripts/reproduce.py")
        return 0
    if len(sys.argv) != 1:
        raise ValueError("No arguments accepted; use --help for usage")
    check()
    for command in ("git", "lean", "lake"):
        if not shutil.which(command):
            raise RuntimeError(f"Install {command} and put it on PATH before reproducing")
    work = ROOT / "reproduction"
    work.mkdir(exist_ok=True)
    destination = Path(tempfile.mkdtemp(prefix="run-", dir=work)) / "directed-cycles-lean"
    shutil.copytree(ROOT / "directed-cycles-lean", destination)
    print(f"Reproduction directory: {destination}", flush=True)
    subprocess.run(["lake", "exe", "cache", "get"], cwd=destination, check=True)
    subprocess.run([sys.executable, "scripts/verify.py", "--certify"],
                   cwd=destination, check=True)
    print(f"Fresh certificate: {destination / 'verification/certificate.json'}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"REPRODUCTION FAILED: {error}", file=sys.stderr)
        sys.exit(1)
