module

public import DirectedCycles.LocalCentralQuotientSmoothInverse
public import DirectedCycles.LocalCentralQuotientSmoothMultiplication
public import DirectedCycles.LocalSmoothnessFromOperationGerms

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles.LocalGroupAlgebra.CentralQuotientData
variable {H E F : Type*} [TopologicalSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : LocalGroupAlgebra H} {P : Set H} (D : L.CentralQuotientData P)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen D.small) (hWa : D.small ⊆ a.target)
    (hrel : ∀ x y : D.small, D.equivalence.Rel x.val y.val ↔ (a.symm x.val).2 = (a.symm y.val).2)

/-- The actual central quotient of a smooth local group is a smooth local
group in its transverse slice atlas. All local topological axioms follow from
the constructed operation germs. -/
theorem algebra_smooth (hL : LocalGroupSmoothness (E := E) L)
    (haSmooth : ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source)
    (haInv : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target) :
    letI := D.sliceChartedSpace a hWo hWa hrel
    LocalGroupSmoothness (E := F) D.algebra := by
  let := D.sliceChartedSpace a hWo hWa hrel
  exact localGroupSmoothness_of_operation_germs D.algebra
    (D.contMDiff_algebra_inv a hWo hWa hrel hL haSmooth haInv)
    (D.exists_smooth_algebra_mul a hWo hWa hrel hL haSmooth haInv)
end DirectedCycles.LocalGroupAlgebra.CentralQuotientData
