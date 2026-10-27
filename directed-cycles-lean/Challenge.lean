module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Nearly linear directed cycles in vertex-transitive digraphs

This is the independently readable statement of Theorem 1.5 of the revised
manuscript by Bowen Li and Abhishek Methuku archived in `manuscript/source.tex`.
That manuscript is intended to replace arXiv:2607.05807v2; the near-linear
statement is not in that earlier public version.

An adjacency relation `D` on `Fin n` describes a finite digraph without
parallel arcs. The first hypothesis excludes loops. The second says that the
underlying undirected graph is connected, using reflexive transitive closure.
The third says that for every pair of vertices there is a permutation taking
one to the other and preserving adjacency in both directions.

A cycle is represented by a natural length `k ≥ 2` and an injective map
`vertex : Fin k ↪ Fin n`. The `finRotate k` condition supplies every directed
arc, including the closing arc. Cycles of length two are allowed. The bound
uses real exponentiation. The threshold is chosen after ε but before n and D.

Only Mathlib is imported. The single deliberate `sorry` is a statement-only
placeholder required by this comparison setup; it is not part of the proof.
`Solution.lean` supplies the same declaration with a proof and does not import
this module. Comparator must reject any unproved assumption in that proof.
This submission concerns Theorem 1.5 and its proof dependencies, not Theorem
1.3, Section 8, Hamiltonicity, or the full directed Lovász conjecture.
-/

public section

namespace DirectedCycles

/-- For every ε > 0, every sufficiently large connected vertex-transitive
loopless digraph has a simple directed cycle of length at least n^(1−ε). -/
theorem nearly_linear_directed_cycles :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ D : Fin n → Fin n → Prop,
        (∀ v, ¬ D v v) →
        (∀ x y, Relation.ReflTransGen (fun u v => D u v ∨ D v u) x y) →
        (∀ x y, ∃ g : Equiv.Perm (Fin n),
          g x = y ∧ ∀ u v, D (g u) (g v) ↔ D u v) →
        ∃ k : ℕ, 2 ≤ k ∧ ∃ vertex : Fin k ↪ Fin n,
          (∀ i, D (vertex i) (vertex (finRotate k i))) ∧
          (n : ℝ) ^ (1 - ε) ≤ (k : ℝ) := by
  sorry

end DirectedCycles
