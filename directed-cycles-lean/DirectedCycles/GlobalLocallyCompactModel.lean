module

public import DirectedCycles.InternalLocallyCompactTopology
public import DirectedCycles.SeparatedLocallyCompactModel

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Pointwise Topology
namespace DirectedCycles

/-- Every sequence of actual finite approximate groups has a genuine
Hausdorff metrizable locally compact quotient model of its generated group.
The internal fourth power has compact image and contains the inverse image
of an identity neighbourhood. No Lie structure is assumed. -/
theorem exists_global_locallyCompact_model (u : Ultrafilter ℕ)
    (hu : (u : Filter ℕ) ≤ Filter.atTop) (G : ℕ → Type*) [∀ i, Group (G i)]
    (A : ∀ i, Finset (G i)) (K : ℝ) (hK : 1 ≤ K)
    (hA : ∀ i, IsApproximateSubgroup K (A i : Set (G i))) :
    let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
    let H := Subgroup.closure B
    Nonempty (LocallyCompactGroupModel H (H.subtype ⁻¹' (B^4))) := by
  classical
  obtain ⟨C⟩ := exists_approximate_root_chain G A K hK hA
  let B := ultraSet (u : Filter ℕ) G (fun i => (A i : Set (G i)))
  let H := Subgroup.closure B
  let S := C.shrinking (u : Filter ℕ) (fun i => (hA i).one_mem)
  let basis := C.modelBasis u (fun i => (hA i).one_mem) (fun i => (hA i).inv_eq_self)
  let : TopologicalSpace H := basis.topology
  let : IsTopologicalGroup H := basis.isTopologicalGroup
  let : (𝓝 (1 : H)).IsCountablyGenerated :=
    (S.subgroup_nhds_basis H (C.shrinking_conjugation u (fun i => (hA i).one_mem)
      (fun i => (hA i).inv_eq_self)) 1).isCountablyGenerated
  have hc : IsCompact (H.subtype ⁻¹' (B^4)) := C.compact_fourth_power u hu K hA
  have hn : H.subtype ⁻¹' (B^4) ∈ 𝓝 (1 : H) := by
    have hs : H.subtype ⁻¹' S.sets 0 ∈ 𝓝 (1 : H) := basis.mem_nhds_one ⟨0,rfl⟩
    exact Filter.mem_of_superset hs (fun x hx =>
      C.shrinking_subset (u : Filter ℕ) (fun i => (hA i).one_mem) 0 hx)
  exact exists_separated_locallyCompact_model (H.subtype ⁻¹' (B^4)) hc hn

end DirectedCycles
