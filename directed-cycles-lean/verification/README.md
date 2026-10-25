# Verification evidence

The current sources use Lean 4.35.0 for Palomar. `lean435-build.json` records
the successful build; it is not a kernel-replay or Palomar certificate.

A current `certificate.json` is issued only by a successful run of
`python3 scripts/verify.py --certify` from the project directory. It records
source hashes, the exact theorem and constant closure, allowed foundational
axioms, and fresh replay by Lean's kernel. It is separate from Palomar's comparison and independent-checker results. If the file is absent, no
current fresh-replay certificate has been issued.

`historical-v1.0.1/` contains the earlier Lean 4.34 evidence. The original
byte-identical source package is `../../release/theorem-1-5-lean-certified.zip`
and is published in release v1.0.1. Those records do not certify changed files.

The Palomar workflow runs the pinned registry pipeline in full mode against
one exact public commit. A passing mechanical preflight is separate from
Palomar intake, editorial review, and permanent registration. Each outcome
must be reported separately and linked to its actual run and commit.

The complete constant graph is distributed as `main-constant-closure.json.gz`
to keep browser downloads manageable. The certificate records both the
uncompressed graph hash and its compressed-file hash. To read it:

```sh
gzip -dc verification/main-constant-closure.json.gz > /tmp/directed-cycles-closure.json
```

The historical graph is compressed the same way. Decompression recovers the
original bytes; the historical certificate itself is unchanged. The original
release archive also retains all original paths and evidence.
