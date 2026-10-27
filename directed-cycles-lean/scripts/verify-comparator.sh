#!/usr/bin/env bash
set -euo pipefail

# Supplemental local comparison using the project's bundled Comparator,
# Lean kernel, NanoDa, and con-ron. This is not the full Palomar pipeline:
# the registry independently authenticates the Challenge, runs controls and
# source checks, and can select a maintainer-pinned con-ron update. The pinned
# full workflow in .github/workflows/palomar-preflight.yml is authoritative
# for preflight. This helper follows PalomarTemplate commit 2891de4c48955af824969a263d31b25e7a9a1406.
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted
# comparator.json: it registers the toolchain's bundled kernels itself. This
# generated copy uses the bundled checkers for this supplemental local check.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field; Palomar rejects it", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

lake exe cache get
lake comparator --config "$config"
