module

public import DirectedCycles.Paths

@[expose] public section

set_option autoImplicit false

namespace DirectedCycles

/-- Manuscript Lemma 3.3. The fibres of `π` are the parts of the partition;
strong connectivity is required for the digraph induced on each fibre. -/
theorem stronglyConnected_parts_cycle_lift {V W : Type*} {D : Digraph V}
    (π : V → W)
    (hstrong : ∀ w, StronglyConnected (fun a b : {x // π x = w} => D a.val b.val))
    (C : Cycle (QuotientDigraph D π)) :
    ∃ L : Cycle D, C.length ≤ L.length := by
  classical
  choose x y hx hy hxy using fun i => (C.arc i).2
  let rotate := finRotate C.length
  let a : ∀ i : Fin C.length, {v // π v = C.vertex i} := fun i =>
    ⟨y (rotate.symm i), by simpa only [rotate, Equiv.apply_symm_apply] using hy (rotate.symm i)⟩
  let b : ∀ i : Fin C.length, {v // π v = C.vertex i} := fun i => ⟨x i, hx i⟩
  let P₀ := fun i => Classical.choice (simplePath_of_reachable (hstrong _ (a i) (b i)))
  let P := fun i => (P₀ i).map
    (⟨Subtype.val, Subtype.val_injective⟩ : {v // π v = C.vertex i} ↪ V)
    (fun _ _ h => h)
  have hfibre : ∀ i v, v ∈ (P i).vertices → π v = C.vertex i := by
    intro i v hv
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
    exact u.property
  have hdisjoint : ∀ i j, i ≠ j → (P i).vertices.Disjoint (P j).vertices := by
    intro i j hij
    apply List.disjoint_left.mpr
    intro v hvi hvj
    exact hij (C.vertex.injective ((hfibre i v hvi).symm.trans (hfibre j v hvj)))
  have hj : ∀ i, ∀ u ∈ (P i).vertices.getLast?,
      ∀ v ∈ (P (finRotate C.length i)).vertices.head?, D u v := by
    intro i u hu v hv
    have hu' : u = x i := by
      simpa only [(P i).last, Function.Embedding.coeFn_mk, b, Subtype.coe_mk, Option.mem_some_iff, eq_comm] using hu
    have hv' : v = y i := by
      simpa only [(P _).head, Function.Embedding.coeFn_mk, a, Subtype.coe_mk, rotate, Equiv.symm_apply_apply, Option.mem_some_iff,
        eq_comm] using hv
    subst u; subst v
    exact hxy i
  obtain ⟨L, _, hL, _⟩ := cycle_of_disjoint_segments C.two_le (fun i => (P i).vertices)
    (fun i => (P i).nonempty) (fun i => (P i).nodup) hdisjoint
    (fun i => (P i).chain) hj
  exact ⟨L, hL⟩

end DirectedCycles
