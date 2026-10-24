import DirectedCycles.LocalGroupSmoothness
import DirectedCycles.LocalSliceSmoothInverse
import DirectedCycles.LocalSliceSmoothMultiplication
import DirectedCycles.LocalQuotientContinuity

set_option autoImplicit false
open scoped Topology Pointwise Manifold ContDiff
namespace DirectedCycles.LocalNormalSet
variable {H E F : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [hLie : LieGroup 𝓘(ℝ,E) ∞ H]
    {P V W : Set H} (hP : LocalNormalSet P V)
    (hW1 : (1 : H) ∈ W) (hWi : W⁻¹ = W) (hW6 : W^6 ⊆ V)
    (a : OpenPartialHomeomorph (ℝ × F) H) (hWo : IsOpen W) (hWa : W ⊆ a.target)
    (hrel : ∀ x ∈ W, ∀ y ∈ W, x*y⁻¹ ∈ P ↔ (a.symm x).2 = (a.symm y).2)

include hLie in
/-- The actual window quotient is a smooth local group in its constructed slice
atlas. Every operation is the previously defined quotient operation. -/
theorem quotientAlgebra_smooth
    (haSmooth : ContMDiffOn 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ a a.source)
    (haInv : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,ℝ × F) ∞ a.symm a.target) :
    letI := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
    LocalGroupSmoothness (E := F) (hP.quotientAlgebra hW1 hWi hW6) := by
  let := hP.sliceChartedSpace hW1 hWi hW6 a hWo hWa hrel
  exact {
    toLocalGroupTopology := hP.quotientAlgebra_topology hW1 hWi hW6 hWo
    smooth_inv := hP.contMDiff_quotientInv_slice hW1 hWi hW6 a hWo hWa hrel haSmooth haInv
    smooth_mul := fun q r hqr => hP.exists_smooth_local_quotient_mul hW1 hWi hW6 a hWo hWa hrel haSmooth haInv q r hqr
  }
end DirectedCycles.LocalNormalSet
