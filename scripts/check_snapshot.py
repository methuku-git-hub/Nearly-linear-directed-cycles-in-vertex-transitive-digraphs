#!/usr/bin/env python3
"""Check the published snapshot's bytes; does not run Lean or issue a certificate."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ARCHIVE_HASH = "68a74340a45818532e8988bab213a4c2112f77b27707de2e451a1cbbdeaf6bcc"
CERTIFICATE_HASH = "4b02d041d2f9076240f6f02787e36fb27453ddf2411ad1cbf252b719f113f1f3"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_name(name):
    p = PurePosixPath(name)
    require(not p.is_absolute() and ".." not in p.parts and "\\" not in name,
            f"Unsafe path: {name}")
    return p


def check(root=ROOT):
    root = Path(root)
    archive = root / "release/theorem-1-5-lean-certified.zip"
    require(digest(archive.read_bytes()) == ARCHIVE_HASH, "Archive SHA-256 differs")
    snapshot = root / "directed-cycles-lean"
    with zipfile.ZipFile(archive) as z:
        names = z.namelist()
        require(len(names) == len(set(names)), "Duplicate archive path")
        archive_files = {}
        for name in names:
            p = safe_name(name)
            require(len(p.parts) > 1 and p.parts[0] == snapshot.name,
                    f"Unexpected archive path: {name}")
            archive_files[str(p.relative_to(snapshot.name))] = z.read(name)
    package = json.loads(archive_files["PACKAGE.json"])
    require(set(archive_files) == set(package["files"]) | {"PACKAGE.json"},
            "Package inventory differs from archive")
    present = set()
    for path in snapshot.rglob("*"):
        require(not path.is_symlink(), f"Symlink in snapshot: {path}")
        if path.is_file():
            name = path.relative_to(snapshot).as_posix()
            present.add(name)
            require(name in archive_files, f"Extra snapshot file: {name}")
            require(path.read_bytes() == archive_files[name], f"Changed snapshot file: {name}")
    require(present == set(archive_files), "Missing expanded snapshot files")
    for name, expected in package["files"].items():
        safe_name(name)
        require(digest(archive_files[name]) == expected, f"Package hash differs: {name}")
    cert_bytes = archive_files["verification/certificate.json"]
    require(digest(cert_bytes) == CERTIFICATE_HASH == package["certificate_sha256"],
            "Certificate hash differs")
    cert = json.loads(cert_bytes)
    require(cert["status"] == "MAIN_THEOREM_AND_CLOSURE_KERNEL_VERIFIED", "Unexpected status")
    require(cert["main_theorem"]["name"] == "DirectedCycles.theorem_1_5", "Wrong target")
    require(cert["main_theorem"]["theorem_present"] and
            cert["main_theorem"]["exact_target_type"], "Target check absent")
    require(cert["fresh_dependency_closure_replay_passed"], "Fresh replay not recorded")
    require(not cert["certificate_refusal_reasons"], "Certificate records a refusal")
    require(set(cert["main_theorem"]["axioms"]) <= ALLOWED, "Unexpected main axiom")
    for table in (cert["files"], cert["evidence_files"]):
        for name, expected in table.items():
            safe_name(name)
            require(name in archive_files and digest(archive_files[name]) == expected,
                    f"Certificate hash differs: {name}")
    closure = json.loads(archive_files[cert["exact_constant_closure"]])
    require(digest(archive_files[cert["exact_constant_closure"]]) ==
            cert["exact_constant_closure_sha256"], "Closure hash differs")
    require(closure["root"] == cert["main_theorem"]["name"] and closure["complete"],
            "Wrong or incomplete recorded closure")
    require(set(closure["axioms"]) <= ALLOWED, "Unexpected recorded closure axiom")
    return len(archive_files)


if __name__ == "__main__":
    try:
        count = check()
    except (OSError, KeyError, ValueError, zipfile.BadZipFile) as error:
        print(f"SNAPSHOT INTEGRITY FAILED: {error}", file=sys.stderr)
        sys.exit(1)
    print(f"Snapshot integrity passed: {count} files match the certified archive.")
    print("This checked recorded evidence and hashes; it did not rerun Lean.")
