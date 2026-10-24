# Theorem 1.5 — Lean formalization and verification

The unconditional proof is `DirectedCycles.theorem_1_5` in
`DirectedCycles/Theorem15.lean`. Its type is `DirectedCycles.MainTheorem`.
**The current certification status is recorded in `verification/certificate.json`
and the generated `blueprint/index.html`. If that certificate is absent, fresh
closure verification has not completed successfully.** A build or a partial
report is not a certificate.

The target is the nearly linear directed-cycle theorem in the supplied
`long_directed_cycles_updated.tex`, Theorem 1.5. The manuscript snapshot and its
provenance are in `manuscript/`. Its SHA-256 is
`d78f34ca5ff88d6d3d5eac3f8dd83beb513c2cb6805ad13c6e0085c16fad20ec`.
The original manuscript was not edited. Its text was treated as mathematical
source material, not instructions.

## Exact statement

For every real ε > 0 there is a natural n₀ such that, for every n ≥ n₀ and
loopless connected vertex-transitive digraph D on `Fin n`, there exists a
simple directed cycle C with `n^(1-ε) ≤ C.length`.

`Digraph` is a binary adjacency relation. `Connected` is connectivity of the
underlying undirected relation. `VertexTransitive` uses adjacency-preserving
permutations in both directions. `Cycle` has length at least two, an injective
vertex map, every consecutive arc, and the closing arc. These definitions are
in `DirectedCycles/Basic.lean`. The threshold is chosen before n and D, and the
power is the real power. The loopless convention is stated in the manuscript.
`Audit.lean` independently spells out the full quantified target and checks that
the main theorem has exactly the named target type.

No structural theorem is a premise of `theorem_1_5`. Earlier conditional
reduction lemmas remain useful intermediate results. Their premises are
supplied by unconditional theorems in `FiniteStructuralTheorems.lean` and
`FiniteCosetNilprogressionTheorem.lean`.

## Proof route and repaired dependencies

The finite coset-nilprogression structure theorem is constructed through an
actual locally compact model, a Lie quotient, finite source windows, and
induction on the dimension of a smooth local target. The zero-dimensional
case is local. The central quotient is constructed with its smooth structure,
dimension drop, good-model properties, controlled lifts, and no-small-subgroups
conclusion. Repeated induction does not assume a global Lie identification,
Lie third theorem, or a general local-group globalization theorem.

Finite strong-group quotients remove the small-subgroup kernel. Ambient word
bounds transfer local progressions to the original finite group; restoring the
kernel preserves the required density. Finite small neighbourhoods sharpen
containment to the fourth power. The ultrafilter counterexample argument gives
uniform finite constants. The finite algebra, normal-orbit structure, and
directed-cycle construction then prove the main theorem.

Other proof repairs include exact retained-position and intersection control
for the return walks, a full tensor interpolation argument valid with torsion,
and finite prime-field character counting in place of an unnecessary stronger
prime-chain assertion. The blueprint retains manuscript correspondence and
historical planned routes. The claimed formalization is the main theorem and
its actual dependency closure; broader literature statements and unused source
assertions are not silently promoted to proved theorems. Theorem 1.3 and Section
8 are outside this target.

## Dependency graph and evidence

- `blueprint/index.html`: navigable, generated project import graph, with library
  imports grouped. Import edges intentionally include helpers unused by the
  final proof term.
- `verification/main-constant-closure.json`: the transitive graph extracted from
  the main theorem's actual kernel constants, traversing types, bodies,
  inductive declarations, constructors, and recursor rules. Inductive metadata
  can create cycles. It includes library declarations and definitions.
- `blueprint/manuscript-map.json`: source statements and corresponding Lean
  declarations, with scope qualifications. Consult the actual Lean types.
- `blueprint/historical-planned-dependencies.json`: the old plan, retained as
  history. Its statuses are not current verification claims.
- `verification/certificate.json`, when present: exact target, axiom audit,
  pinned versions, source and evidence hashes, module replay, and fresh imported
  environment replay. Historical partial reports are explicitly archived.

The only permitted foundational axioms are Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. The checker rejects `sorryAx` and every
other axiom in the main closure and project theorems. It also rejects unsafe
constants in the main closure and proof escapes in mathematical source files.
The independent closure traversal is compared with Lean's cached axiom audit.
Verification infrastructure is not imported by the mathematics.

Fresh replay uses Lean's own kernel, not a second independently implemented
kernel. No computational examples or source compilation are substituted for
proof verification.

## Reproduce

Requirements: Lean 4.34.0 (commit
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`), Git, and Python 3. Mathlib is pinned
to `5ed2965256430c3649e86755f9576b54eca72435`; all transitive package revisions
are pinned in `lake-manifest.json`. With `elan`, `lean-toolchain` selects Lean.
From this directory run:

```sh
lake exe cache get
python3 scripts/verify.py --certify
```

A new checkout needs network access to obtain the pinned packages and cache.
The source package excludes toolchain binaries, dependency checkouts, and build
products. The verification command builds the project, checks the exact target
and all project theorem axioms, generates the complete constant inventory and
import graph, and verifies that the root imports every project module exactly once. It runs
`lake env leanchecker --fresh --verbose DirectedCycles`, checking the entire
imported environment in an empty Lean kernel environment. Source hashes and
dependency revisions are rechecked after replay. Only successful completion
writes the current certificate and sets the blueprint's verified flags.

`python3 scripts/verify.py --partial` performs the preliminary checks and
sequential module replay, but never issues a certificate. Certification uses
fresh replay of the entire imported environment, which also checks the project
modules and avoids repeatedly loading the same imports for each module. Starting any new run invalidates a
previous current certificate and resets the active blueprint to pending.
