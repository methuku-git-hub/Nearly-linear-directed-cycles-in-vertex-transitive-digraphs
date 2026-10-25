# Nearly linear directed cycles in vertex-transitive digraphs

**Bowen Li and Abhishek Methuku**

**First publicly released: 24 October 2026**

**Palomar preparation branch:** This project uses Lean 4.35.0 and includes
an independent statement, a proved solution, and the pinned full Palomar
verification workflow. Check the [current evidence](directed-cycles-lean/verification/README.md)
and the Actions run for the exact commit. The earlier certificate applies
only to release v1.0.1; adding submission files does not establish Palomar
verification or registration.

[Manuscript snapshot](directed-cycles-lean/manuscript/source.tex) ·
[Lean proof](directed-cycles-lean/DirectedCycles/Theorem15.lean) ·
[Download](https://github.com/methuku-git-hub/Nearly-linear-directed-cycles-in-vertex-transitive-digraphs/releases/tag/v1.0.1) ·
[Verification](#verification)

This Lean project formalizes the near-linear directed-cycle theorem
(Theorem 1.5) in the archived revised manuscript and every dependency of its
Lean proof:

> For every real $\varepsilon > 0$, there exists $n_0$ such that every
> connected vertex-transitive digraph on $n \ge n_0$ vertices contains a
> simple directed cycle of length at least $n^{1-\varepsilon}$.

Digraphs are finite, have no loops or parallel arcs, and may have arcs in both
directions. Connectedness refers to the underlying undirected graph. Cycles
have distinct vertices and include the closing arc; length two is allowed.
These are the manuscript conventions. The precise Lean definitions are in
[`Basic.lean`](directed-cycles-lean/DirectedCycles/Basic.lean); the main Lean
declaration is
[`DirectedCycles.theorem_1_5`](directed-cycles-lean/DirectedCycles/Theorem15.lean).
The full proof development is in [`directed-cycles-lean/`](directed-cycles-lean).

## Manuscript version and scope

**Publication status:** This revised manuscript is not yet on arXiv. The authors
plan to upload it soon as a replacement for
[arXiv version 2](https://arxiv.org/abs/2607.05807v2).

The reference text is the [archived revised manuscript](directed-cycles-lean/manuscript/source.tex).
Its title and author order match those above. Theorem numbers and the
[manuscript correspondence](directed-cycles-lean/blueprint/manuscript-map.json)
refer to this exact snapshot, identified by SHA-256 in
[`manuscript/provenance.json`](directed-cycles-lean/manuscript/provenance.json).

The earlier public [arXiv version 2](https://arxiv.org/abs/2607.05807v2), dated
19 August 2026, is titled *Long directed cycles in vertex-transitive digraphs*
and states a lower bound of $\Omega(\sqrt n)$. The near-linear
statement in this formalization belongs to the revised manuscript archived above.
The historical certificate applies to the v1.0.1 sources and pinned dependencies.
Release v1.0.1 adopts the new title throughout the manuscript, PDF metadata,
project documentation, and blueprint, with a fresh certificate. The Lean
proof files and mathematical manuscript text are unchanged from v1.0.0.

The scope is Theorem 1.5 and its actual proof dependencies. Theorem 1.3 and
Section 8 (the perimeter-gap construction) are outside this formalization.
The Lean proof includes repaired arguments and replacement lemmas, documented
in the [project README](directed-cycles-lean/README.md) and
[blueprint](directed-cycles-lean/blueprint/dependencies.json).
[Unused stronger source statements](directed-cycles-lean/blueprint/source-statements-not-used.json)
are identified separately, including the full layer bound in Lemma 6.2 and
the explicit quotient-chain assertion in Lemma 6.3.

## Verification

The [v1.0.1 release](https://github.com/methuku-git-hub/Nearly-linear-directed-cycles-in-vertex-transitive-digraphs/releases/tag/v1.0.1)
records a successful fresh Lean kernel replay on **24 October 2026** using
Lean 4.34.0, along with separate clean-build evidence. Its archive remains
unchanged. Historical evidence is labelled in
[`verification/`](directed-cycles-lean/verification/README.md).

The Palomar port uses Lean 4.35.0 and matching pinned Mathlib dependencies.
[`Challenge.lean`](directed-cycles-lean/Challenge.lean) independently spells
out the theorem using ordinary relations, permutations, and an injective cycle
sequence. Its one deliberate statement-only `sorry` is excluded from the
proof. [`Solution.lean`](directed-cycles-lean/Solution.lean) proves that exact
statement using the existing development and does not import Challenge.
Comparator must check the same declaration name and type and allow only
`propext`, `Classical.choice`, and `Quot.sound` in the proved result.

The [Palomar workflow](.github/workflows/palomar-preflight.yml) invokes the
registry's complete pinned mechanical pipeline in Linux. A passing preflight,
registry verification, editorial review, and registration are separate stages.
The full workflow report for the exact commit records its mechanical outcome;
it does not itself register a project. See [`PALOMAR.md`](PALOMAR.md) for
submission paths and the verification procedure.

## Reproduce the verification

Install Git, Python 3, and [elan](https://github.com/leanprover/elan), with
`lean` and `lake` on your PATH. The current project pins Lean 4.35.0 and all
library revisions. To check the current port:

```sh
git clone --branch palomar-verification https://github.com/methuku-git-hub/Nearly-linear-directed-cycles-in-vertex-transitive-digraphs.git
cd Nearly-linear-directed-cycles-in-vertex-transitive-digraphs
python3 scripts/check_snapshot.py
cd directed-cycles-lean
lake exe cache get
lake build
lake build Palomar
# Linux with bubblewrap installed:
bash scripts/verify-comparator.sh
```

The archive-integrity script checks only the historical release package.
To replay that original package with Lean 4.34.0, return to the repository root
and run `python3 scripts/reproduce.py`; it extracts a new copy under
`reproduction/`. To run the project's own fresh Lean kernel replay on the
current port, use this inside `directed-cycles-lean/`:

```sh
python3 scripts/verify.py --certify
```

That procedure checks the exact main statement and axioms, extracts the actual
constant dependency graph, and runs fresh replay using Lean's own kernel.
It writes a new certificate only after all its checks succeed. It is separate
from Palomar's Comparator and independently implemented kernel checks.

Network access is required to obtain pinned dependencies. Full builds and
verification can require substantial time, disk space, and memory.

## Explore the proof

| Resource | Contents |
| --- | --- |
| [Detailed project README](directed-cycles-lean/README.md) | Proof route, repaired arguments, and verification details |
| [Dependency blueprint](directed-cycles-lean/blueprint/index.html) | Navigable import graph; download and open locally |
| [Constant dependency graph](directed-cycles-lean/verification/main-constant-closure.json.gz) | Complete Lean 4.35 theorem dependency graph, losslessly compressed |
| [Manuscript correspondence](directed-cycles-lean/blueprint/manuscript-map.json) | Source statements and their Lean declarations |
| [Certified source archive](release/theorem-1-5-lean-certified.zip) · [SHA-256](release/SHA256SUMS) | Original source package, certificate, and evidence |

The formalization covers Theorem 1.5 and its actual dependency closure.
Proof repairs and the scope of the literature inputs are explained in the
project README. The blueprint's import graph includes helper modules; the
constant graph records dependencies of the proof itself.

## Credits and provenance

The mathematical paper is by **Bowen Li and Abhishek Methuku**. The Lean
development and verification tooling were produced with OpenAI Codex for
Abhishek Methuku. Lean, Mathlib, and other external dependencies retain their
own licenses.

The historical certified project is preserved in the archive in `release/`.
The working sources in `directed-cycles-lean/` are the
Palomar port under verification; see the status above for checks actually completed. The
[v1.0.1 release](https://github.com/methuku-git-hub/Nearly-linear-directed-cycles-in-vertex-transitive-digraphs/releases/tag/v1.0.1)
retains the certified source package and its original evidence.

The Lean code and verification tools are licensed under [Apache-2.0](LICENSE).
The manuscript, cited papers, and dependencies retain their existing rights;
see [NOTICE](NOTICE).
