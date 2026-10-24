import DirectedCycles.GleasonCoordinates
import DirectedCycles.NormedAlgebraOneParameter

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The adjoint action along each actual one-parameter subgroup is a
smooth curve in the finite-dimensional operator algebra. -/
theorem coordinateAdjoint_curve_contDiff (x : GleasonLieAlgebra D) :
    ContDiff ℝ ∞ (fun t : ℝ => coordinateAdjoint D e ((toOneParameter D x).eval t)) := by
  apply normedAlgebra_one_parameter_contDiff
  · simpa only [OneParameter.eval_zero] using coordinateAdjoint_one D e
  · exact ((continuous_coordinateAdjoint D e).comp (toOneParameter D x).continuous_eval).continuousAt
  · intro s t
    rw [OneParameter.eval_add,coordinateAdjoint_mul]

end DirectedCycles.GleasonLieAlgebra
