# Palomar verification

This branch prepares Theorem 1.5 for Palomar. A local build, the historical
release certificate, a successful mechanical preflight, editorial review,
and permanent registry publication are distinct outcomes. No Palomar result
is claimed until a linked report for the exact commit records it.

## Recorded mechanical verification

The public commit `16f43c7731a2d973e989c5e9006b62088dd3068d` passed both the
[full project preflight](https://github.com/methuku-git-hub/Nearly-linear-directed-cycles-in-vertex-transitive-digraphs/actions/runs/40160159378)
and [Palomar's mechanical verification for submission 9pdru5dwljmt](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/40162833371)
on 25 October 2026. The preflight report records no errors or warnings and
acceptance by Lean, NanoDa, and con-ron. Those reports certify the identified
snapshot, not later commits. They do not establish editorial approval or
permanent registry registration.

The 26 October audit corrects provenance and documentation only. All Lean
sources, the Challenge and Solution statements, the comparator configuration,
the manuscript, and dependency pins are unchanged. A new public commit still
requires a passing full preflight before it is used for a new submission.

## Statement and proof

The selected Lake project is `directed-cycles-lean/`.

- `Challenge.lean` is a short, independent statement importing only Mathlib.
  It describes looplessness, undirected connectedness, vertex transitivity,
  and a simple directed cycle with its closing arc. The threshold is chosen
  after epsilon and before the graph order and adjacency relation. Its one
  deliberate `sorry` is a statement placeholder, authorized by the maintainer.
- `Solution.lean` proves the same declaration,
  `DirectedCycles.nearly_linear_directed_cycles`, by applying
  `DirectedCycles.theorem_1_5` and translating its structures into the explicit
  hypotheses and witness. Solution does not import Challenge.
- `comparator.json` selects this single theorem and permits only `propext`,
  `Classical.choice`, and `Quot.sound` in the proof.
- `formalization.yaml` records the exact source, proof repairs, scope,
  mathematical authorship, formalization responsibility, automation, and review.

## Versions and historical evidence

This port pins Lean 4.35.0, compiler commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The Mathlib revision uses exactly
the same Lean version. The complete dependency manifest is committed.

All regular Lean files use the module system. The source port makes public
interfaces and definition bodies explicit; direct imports are added where
needed. The archived manuscript text is unchanged.

Release v1.0.1 and `release/theorem-1-5-lean-certified.zip` preserve the earlier
Lean 4.34 sources and certificate. Evidence copied from that release is
labelled historical in `directed-cycles-lean/verification/historical-v1.0.1/`.
It does not certify the port. The current port's certificate and generated
blueprint are in `directed-cycles-lean/verification/certificate.json` and
`directed-cycles-lean/blueprint/`. Their hashes identify their exact inputs;
they are distinct from Palomar's mechanical reports.

## Reproduce checks

With Git, Python 3, and elan installed:

```sh
python3 scripts/check_submission_sources.py
python3 scripts/check_snapshot.py
cd directed-cycles-lean
lake exe cache get
lake build
lake build Palomar
```

The Challenge build deliberately emits one `sorry` warning. No such placeholder
is permitted in Solution or its proof dependencies. On Linux with `bwrap`
(bubblewrap) installed, also run:

```sh
bash scripts/verify-comparator.sh
```

This script follows Palomar's template at commit
`2891de4c48955af824969a263d31b25e7a9a1406`. It invokes the Comparator bundled
with the selected toolchain and registers its bundled NanoDa and con-ron
checkers. This is a supplemental local check. The full registry pipeline also
authenticates and isolates the Challenge, runs positive and negative controls,
checks source and metadata requirements, and may use a maintainer-pinned
con-ron update. The standalone script is not equivalent to that full pipeline.

The complete mechanical preflight is the GitHub Actions workflow
`.github/workflows/palomar-preflight.yml`. It pins both the reusable workflow
and its `pipeline_commit` to PalomarSubmission commit
`c02bbeaed888df45c4e28c4e99dba540ad21552a`, uses `mode: full`, and selects
`palomar-standard-v1`. For pull requests it checks the exact head commit,
not an automatically generated merge commit. This is the required preflight;
the standalone commands above do not replace it.

## Submission fields

Only after the full mechanical report passes, submit this repository and the
full 40-character SHA of the exact prepared public commit:

| Field | Value |
| --- | --- |
| Repository | `methuku-git-hub/Nearly-linear-directed-cycles-in-vertex-transitive-digraphs` |
| Project path | `directed-cycles-lean` |
| Comparator path | `directed-cycles-lean/comparator.json` |
| Metadata path | `directed-cycles-lean/formalization.yaml` |
| Responsible maintainer | Abhishek Methuku |

The actual commit must be copied from the passing run; a branch name or release
tag is insufficient. Registry intake and permanent registration have not been
performed merely by adding these files. Follow the current
[submission instructions](https://palomar-registry.org/how-to-submit) and
[agent protocol](https://submit.palomar-registry.org/llms.txt).

## Licence and review

The Lean code and verification tools are licensed under Apache-2.0. The
manuscript and cited works retain their existing rights; see `NOTICE`.
Mathematical authorship belongs to Bowen Li and Abhishek Methuku. Abhishek
Methuku directed and maintains the formalization, whose proofs and tooling
were produced with Codex. No independent human audit of the complete formal
development is recorded. Automated checks must not be described as human review.
