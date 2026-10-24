import DirectedCycles.SubgroupNSSBasics
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Group.Subgroup

set_option autoImplicit false
namespace DirectedCycles
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]

/-- In a locally compact group, subgroup trapping produces an actual
compact containing subgroup inside every prescribed identity neighbourhood. -/
theorem compact_subgroup_of_trapping (htrap : HasSubgroupTrapping G)
    (U : Set G) (hU : IsOpen U) (hU1 : (1 : G) ∈ U) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∃ H : Subgroup G, IsCompact (H : Set G) ∧ (H : Set G) ⊆ U ∧
        ∀ S : Subgroup G, (S : Set G) ⊆ V → S ≤ H := by
  obtain ⟨C,hC,hC1,hCU⟩ := exists_compact_subset hU hU1
  obtain ⟨V,hV,hV1,H,hHC,htrapH⟩ := htrap (interior C) isOpen_interior hC1
  have hcl : (H.topologicalClosure : Set G) ⊆ C :=
    closure_minimal (hHC.trans interior_subset) hC.isClosed
  refine ⟨V,hV,hV1,H.topologicalClosure,
    hC.of_isClosed_subset H.isClosed_topologicalClosure hcl,hcl.trans hCU,?_⟩
  intro S hS
  exact (htrapH S hS).trans H.le_topologicalClosure
end DirectedCycles
