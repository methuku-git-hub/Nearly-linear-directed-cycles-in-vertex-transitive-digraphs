# Long directed cycles in vertex-transitive digraphs

**Bowen Li and Abhishek Methuku**

[Manuscript](directed-cycles-lean/manuscript/source.tex) ·
[Lean proof](directed-cycles-lean/DirectedCycles/Theorem15.lean) ·
[Download](https://github.com/methuku-git-hub/Directed-Lovasz-conjecture/releases/tag/v1.0.0) ·
[Verification](#verification)

This Lean project formalizes the paper's near-linear directed-cycle theorem
(Theorem 1.5) and its dependencies:

> For every $\varepsilon > 0$, every sufficiently large connected
> vertex-transitive digraph on $n$ vertices contains a simple directed cycle
> of length at least $n^{1-\varepsilon}$.

Digraphs are loopless, and connectedness refers to the underlying undirected
graph. The precise definitions are in
[`Basic.lean`](directed-cycles-lean/DirectedCycles/Basic.lean); the main Lean
declaration is
[`DirectedCycles.theorem_1_5`](directed-cycles-lean/DirectedCycles/Theorem15.lean).
The full proof development is in [`directed-cycles-lean/`](directed-cycles-lean).

## Verification

The [published certificate](directed-cycles-lean/verification/certificate.json)
records a successful fresh Lean kernel replay of the main theorem and its
dependency closure on **24 October 2026**. A separate
[clean rebuild](directed-cycles-lean/verification/clean-source-rebuild.json)
of the project sources reproduced the constant dependency graph.

The proof contains no `sorry` or additional mathematical axioms. Its only
foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Replay uses Lean's own kernel. The certificate records the verification;
the source and pinned dependencies let readers reproduce it.

## Reproduce the verification

Install Git, Python 3, and [elan](https://github.com/leanprover/elan), with
`lean` and `lake` on your PATH. Lean 4.34.0 and all library revisions are pinned
in the project.

```sh
git clone https://github.com/methuku-git-hub/Directed-Lovasz-conjecture.git
cd Directed-Lovasz-conjecture
python3 scripts/check_snapshot.py
python3 scripts/reproduce.py
```

The first script checks the published files against the certified archive.
The second makes a working copy under `reproduction/` and runs the original
verification procedure:

```sh
lake exe cache get
python3 scripts/verify.py --certify
```

This builds the sources, checks the exact theorem statement and allowed
axioms, extracts the dependency closure, and runs
`lake env leanchecker --fresh --verbose DirectedCycles`. A new certificate
is written only after all checks pass. The published snapshot is preserved.

Network access is needed to obtain the pinned dependencies. A full build and
replay can require substantial time and memory; the original verification ran
on macOS arm64. The GitHub workflow checks **snapshot integrity**, rather than
performing a new kernel replay.

## Explore the proof

| Resource | Contents |
| --- | --- |
| [Detailed project README](directed-cycles-lean/README.md) | Proof route, repaired arguments, and verification details |
| [Dependency blueprint](directed-cycles-lean/blueprint/index.html) | Navigable import graph; download and open locally |
| [Constant dependency graph](directed-cycles-lean/verification/main-constant-closure.json) | The main theorem's actual transitive dependencies |
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

The certified project under `directed-cycles-lean/` is preserved byte for byte.
The repository's presentation and integrity tools are maintained separately.
For an immutable reference, use a full commit permalink from the repository's
history.
