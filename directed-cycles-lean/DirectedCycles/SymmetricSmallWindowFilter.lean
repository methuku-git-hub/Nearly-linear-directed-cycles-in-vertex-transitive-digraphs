module

public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology Pointwise
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual filter of shrinking open symmetric identity windows. -/
def symmetricWindowFilter : Filter (Set G) :=
  (𝓝 (1 : G)).smallSets ⊓ 𝓟 {V : Set G | IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V}

/-- Every identity neighbourhood contains such a window, so the filter
is proper; no countable basis or metrizable reduction is needed. -/
theorem symmetricWindowFilter_neBot : (symmetricWindowFilter (G := G)).NeBot := by
  apply frequently_mem_iff_neBot.mp
  apply frequently_smallSets.mpr
  intro U hU
  obtain ⟨O,hOU,hO,hO1⟩ := mem_nhds_iff.mp hU
  let V := O ∩ O⁻¹
  have hV1 : (1 : G) ∈ V := ⟨hO1,by simpa using hO1⟩
  have hVi : V⁻¹ = V := by
    ext z
    change (z⁻¹ ∈ O ∧ (z⁻¹)⁻¹ ∈ O) ↔ (z ∈ O ∧ z⁻¹ ∈ O)
    simp only [inv_inv,and_comm]
  exact ⟨V,Set.inter_subset_left.trans hOU,hO.inter hO.inv,hV1,hVi⟩

/-- An ultrafilter refining these windows supplies compact limits in
arbitrary locally compact groups, without adding a sequential hypothesis. -/
noncomputable def symmetricWindowUltrafilter : Ultrafilter (Set G) := by
  let := symmetricWindowFilter_neBot (G := G)
  exact Ultrafilter.of (symmetricWindowFilter (G := G))

theorem symmetricWindowUltrafilter_le :
    (symmetricWindowUltrafilter (G := G) : Filter (Set G)) ≤ symmetricWindowFilter := by
  let := symmetricWindowFilter_neBot (G := G)
  exact Ultrafilter.of_le _

theorem symmetricWindowUltrafilter_windows :
    ∀ᶠ V in (symmetricWindowUltrafilter (G := G) : Filter (Set G)),
      IsOpen V ∧ (1 : G) ∈ V ∧ V⁻¹ = V :=
  (symmetricWindowUltrafilter_le.trans inf_le_right) (Filter.mem_principal_self _)

theorem symmetricWindowUltrafilter_small {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∀ᶠ V in (symmetricWindowUltrafilter (G := G) : Filter (Set G)), V ⊆ U :=
  (symmetricWindowUltrafilter_le.trans inf_le_left) (eventually_smallSets_subset.mpr hU)
end DirectedCycles
