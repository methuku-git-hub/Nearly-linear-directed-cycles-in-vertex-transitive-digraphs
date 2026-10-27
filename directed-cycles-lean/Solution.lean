module

public import DirectedCycles.Theorem15

/-!
# Palomar solution: nearly linear directed cycles

This wrapper unfolds the graph hypotheses and cycle witness into ordinary
relations, permutations, and an injective finite vertex sequence. It proves
the independently stated Palomar target using the manuscript theorem.
It does not import the statement-only Challenge module.
-/

public section

namespace DirectedCycles

/-- Every sufficiently large connected vertex-transitive loopless finite
digraph has a simple directed cycle of length at least `n ^ (1 - ε)`.
Connectivity is undirected; the cycle includes its closing arc. -/
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
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := theorem_1_5 ε hε
  refine ⟨n₀, ?_⟩
  intro n hn D hloop hconn htrans
  have ht : VertexTransitive D := by
    intro x y
    obtain ⟨g, hg, hD⟩ := htrans x y
    exact ⟨⟨g, hD⟩, hg⟩
  obtain ⟨C, hC⟩ := hn₀ n hn D hloop hconn ht
  exact ⟨C.length, C.two_le, C.vertex, C.arc, hC⟩

end DirectedCycles
