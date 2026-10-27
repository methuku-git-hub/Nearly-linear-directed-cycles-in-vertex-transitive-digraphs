module

public import DirectedCycles.Paths
public import DirectedCycles.DigraphAutomorphismGroup
public import DirectedCycles.PermutationImage
public import DirectedCycles.NilpotentRanks

@[expose] public section

set_option autoImplicit false
namespace DirectedCycles

theorem induced_action_invariant {G V : Type*} [Group G] [MulAction G V]
    (X : Digraph V) (hX : ∀ g : G, ∀ x y, X (g • x) (g • y) ↔ X x y) :
    ∀ g : PermutationImage G V, ∀ x y, X (g • x) (g • y) ↔ X x y := by
  intro g x y
  obtain ⟨a,ha⟩ := g.property
  change X (g.val x) (g.val y) ↔ X x y
  rw [← ha]
  exact hX a x y

theorem induced_action_transitive {G V : Type*} [Group G] [MulAction G V]
    (ht : ∀ x y : V, ∃ g : G, g • x = y) :
    ∀ x y : V, ∃ g : PermutationImage G V, g • x = y := by
  intro x y
  obtain ⟨g,hg⟩ := ht x y
  exact ⟨⟨MulAction.toPerm g,⟨g,rfl⟩⟩,hg⟩

/-- The finite consequence of manuscript Theorem 3.5 needed by the main
proof. Its proof is finite_structural_input in FiniteStructuralTheorems.
Its nilpotent group lies in the actual induced permutation group. -/
def FiniteStructuralInput : Prop :=
  ∀ lam : ℝ, 0 < lam → lam < 1 →
    ∃ B r c I n₀ : ℕ, 1 ≤ B ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ X : Digraph (Fin n), Loopless X → Connected X → VertexTransitive X →
      ∃ (H : Subgroup (automorphismGroup X)) (hH : H.Normal),
        letI := hH
        (∀ x y, MulAction.orbitRel H (Fin n) x y →
          ∃ P : SimplePath (fun u v => X u v ∨ X v u) x y, (P.length : ℝ) ≤ (n : ℝ)^lam) ∧
        (letI := normalOrbitAction (V := Fin n) H
         let Ω := Quotient (MulAction.orbitRel H (Fin n))
         let K := PermutationImage (automorphismGroup X) Ω
         (∀ x : Ω, Nat.card (MulAction.stabilizer K x) ≤ B) ∧
         ∃ (N : Subgroup K) (_hN : N.Normal) (_hNil : Group.IsNilpotent N),
           Group.rank N ≤ r ∧ Group.nilpotencyClass N ≤ c ∧ N.index ≤ I)

end DirectedCycles
