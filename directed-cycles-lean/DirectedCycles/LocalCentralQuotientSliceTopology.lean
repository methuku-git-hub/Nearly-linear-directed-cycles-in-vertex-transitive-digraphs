import DirectedCycles.LocalCentralQuotientSliceHomeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H F : Type*} [TopologicalSpace H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)

/-- The actual central quotient is Hausdorff and locally compact via its
constructed homeomorphism to an open finite-dimensional slice. -/
theorem slice_topology (a : OpenPartialHomeomorph (ℝ × F) H)
    (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2) :
    T2Space D.Carrier ∧ LocallyCompactSpace D.Carrier := by
  let e := D.sliceHomeomorph a hWo hWa hrel
  let := (DirectedCycles.LocalNormalSet.isOpen_slice_range a hWo hWa).locallyCompactSpace
  exact ⟨e.symm.t2Space,e.locallyCompactSpace_iff.mpr inferInstance⟩
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
