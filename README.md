# Theorem 1.5: long directed cycles in vertex-transitive digraphs

Lean formalization of Theorem 1.5 of **Long directed cycles in vertex-transitive
digraphs**, by Bowen Li and Abhishek Methuku.

For every real ε > 0, there is n₀ such that every loopless connected
vertex-transitive digraph on n ≥ n₀ vertices contains a simple directed cycle
of length at least n^(1−ε). Connectedness means connectedness of the underlying
undirected graph. See the [exact definitions](directed-cycles-lean/DirectedCycles/Basic.lean)
and the [main theorem](directed-cycles-lean/DirectedCycles/Theorem15.lean).

The published snapshot records a successful fresh Lean kernel replay of
`DirectedCycles.theorem_1_5` and its dependency closure on 24 October 2026.
A separate clean rebuild of the project sources reproduced the constant
dependency graph. The proof has no `sorry` or additional mathematical axioms;
its foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Source, certificate, and scope

- [Download the original certified source ZIP](release/theorem-1-5-lean-certified.zip)
  and [SHA-256 checksum](release/SHA256SUMS).
- [Browse the complete project](directed-cycles-lean), including its
  [detailed verification README](directed-cycles-lean/README.md).
- [Certificate](directed-cycles-lean/verification/certificate.json),
  [exact constant dependency graph](directed-cycles-lean/verification/main-constant-closure.json),
  and [clean rebuild record](directed-cycles-lean/verification/clean-source-rebuild.json).
- [Blueprint HTML](directed-cycles-lean/blueprint/index.html): download the
  repository and open this file locally. Its import graph is deliberately an
  overapproximation; the constant dependency graph records the proof's actual
  transitive dependencies.
- [Manuscript snapshot](directed-cycles-lean/manuscript/source.tex) and
  [statement-to-Lean map](directed-cycles-lean/blueprint/manuscript-map.json).

The claim concerns **Theorem 1.5 and its actual dependencies**, not every result
in the manuscript or the full general statements of all cited literature.
The proof includes repairs and alternative arguments described in the project
README. Replay uses Lean's own kernel, not a second independently implemented
kernel. The certificate is a record of checks; readers can rerun those checks
from the source.

## Reproduce

Requirements: Git, Python 3, and [elan](https://github.com/leanprover/elan)
with its `lean` and `lake` commands on PATH. The project pins Lean 4.34.0 and
every library revision. Network access is needed to obtain them.

```sh
git clone https://github.com/methuku-git-hub/Directed-Lovasz-conjecture.git
cd Directed-Lovasz-conjecture
python3 scripts/check_snapshot.py
python3 scripts/reproduce.py
```

`check_snapshot.py` checks that the published archive, expanded files,
certificate, and evidence hashes agree. **This is an integrity check, not a
new proof verification.** `reproduce.py` then copies the snapshot to a new
directory under `reproduction/` and runs:

```sh
lake exe cache get
python3 scripts/verify.py --certify
```

That command builds the Lean sources, checks the exact target and allowed
axioms, extracts the dependency closure, and runs
`lake env leanchecker --fresh --verbose DirectedCycles`. It issues a new
certificate only if all checks pass. The original published snapshot stays
unchanged. A full build and replay can require substantial time and memory;
the original verification ran on macOS arm64. No hosted-runner resource
requirement or independent Linux replay is claimed here.

For an immutable citation, open the repository's commit history and use the
full commit permalink. Tags and the default branch can move.

## Provenance

The Lean development and verification tooling were produced with OpenAI
Codex for Abhishek Methuku. The mathematical manuscript is credited to
Bowen Li and Abhishek Methuku. The certified project is preserved byte for
byte under `directed-cycles-lean/`; repository presentation and integrity
tools live outside that directory and are not part of the old certificate.
Lean, Mathlib, and other external dependencies retain their own licenses.

The automated repository workflow checks snapshot integrity. Its success
must not be described as a fresh kernel replay or external registry approval.
