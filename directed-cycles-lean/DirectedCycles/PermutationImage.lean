import DirectedCycles.SparseInvariant

set_option autoImplicit false
open scoped Classical
namespace DirectedCycles

/-- The actual permutation group induced by a possibly nonfaithful action. -/
abbrev PermutationImage (G V : Type*) [Group G] [MulAction G V] :=
  (MulAction.toPermHom G V).range

/-- Applying Lemma 4.3 to the image permutation group uses the stabilizers
of the induced action, rather than the larger stabilizers in the original group. -/
theorem sparse_subdigraph_of_induced_stabilizers {G V : Type*} [Group G]
    [Fintype V] [MulAction G V]
    (D : Digraph V) (hloop : Loopless D) (hstrong : StronglyConnected D)
    (hD : ∀ (g : G) x y, D (g • x) (g • y) ↔ D x y)
    (ht : ∀ x y : V, ∃ g : G, g • x = y) (hq : 2 ≤ Fintype.card V)
    (B : ℕ) (hB : ∀ a : V, Fintype.card (MulAction.stabilizer (PermutationImage G V) a) ≤ B) :
    ∃ E : Digraph V, ∃ d : ℕ, (∀ x y, E x y → D x y) ∧ Loopless E ∧
      (∀ (g : G) x y, E (g • x) (g • y) ↔ E x y) ∧ StronglyConnected E ∧
      (∀ x, (Finset.univ.filter (E x)).card = d) ∧
      (∀ y, (Finset.univ.filter (fun x => E x y)).card = d) ∧
      1 ≤ d ∧ d ≤ B * ⌈(Real.log (Fintype.card V : ℝ) / Real.log 2)⌉₊ := by
  let K := PermutationImage G V
  have hK : ∀ (g : K) x y, D (g • x) (g • y) ↔ D x y := by
    intro g x y
    obtain ⟨h, hh⟩ := g.property
    change D (g.val x) (g.val y) ↔ D x y
    rw [← hh]
    exact hD h x y
  have htK : ∀ x y : V, ∃ g : K, g • x = y := by
    intro x y
    obtain ⟨g, hg⟩ := ht x y
    exact ⟨⟨MulAction.toPerm g, ⟨g, rfl⟩⟩, hg⟩
  obtain ⟨E, d, hED, hEl, hEi, hEs, hout, hin, hd, hbound⟩ :=
    sparse_invariant_subdigraph D hloop hstrong hK htK hq B hB
  refine ⟨E, d, hED, hEl, ?_, hEs, hout, hin, hd, hbound⟩
  intro g x y
  exact hEi ⟨MulAction.toPerm g, ⟨g, rfl⟩⟩ x y

end DirectedCycles
