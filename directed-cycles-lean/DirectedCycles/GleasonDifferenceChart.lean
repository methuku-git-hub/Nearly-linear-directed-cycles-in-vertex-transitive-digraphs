import DirectedCycles.GleasonTranslationDerivative

set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The actual chart for the left difference at a given base point. -/
noncomputable def coordinateDifferenceChart (x : E) : OpenPartialHomeomorph E E :=
  ((coordinateChart D e).trans (Homeomorph.mulLeft ((coordinateExp D e x)⁻¹)).toOpenPartialHomeomorph).trans
    (coordinateChart D e).symm

theorem coordinateDifferenceChart_apply (x y : E) :
    coordinateDifferenceChart D e x y = coordinateLeftDifference D e x y := by
  change coordinateLog D e ((coordinateExp D e x)⁻¹*((coordinateChart D e) y)) = _
  rw [coordinateChart_coe]
  rfl

theorem coordinateDifferenceChart_symm_apply (x y : E) :
    (coordinateDifferenceChart D e x).symm y = coordinateMul D e (x,y) := by
  change coordinateLog D e (((coordinateExp D e x)⁻¹)⁻¹*((coordinateChart D e) y)) = _
  rw [inv_inv,coordinateChart_coe]
  rfl

theorem coordinateDifferenceChart_base_mem_source {x : E} (hx : x ∈ (coordinateChart D e).source) :
    x ∈ (coordinateDifferenceChart D e x).source := by
  change (x ∈ (coordinateChart D e).source ∧ (coordinateChart D e) x ∈ Set.univ) ∧
    (coordinateExp D e x)⁻¹*((coordinateChart D e) x) ∈ (coordinateChart D e).target
  rw [coordinateChart_coe]
  exact ⟨⟨hx,Set.mem_univ _⟩,by simpa only [inv_mul_cancel] using one_mem_coordinateChart_target D e⟩

theorem coordinateDifferenceChart_zero_mem_target {x : E} (hx : x ∈ (coordinateChart D e).source) :
    (0 : E) ∈ (coordinateDifferenceChart D e x).target := by
  have h := (coordinateDifferenceChart D e x).map_source (coordinateDifferenceChart_base_mem_source D e hx)
  simpa only [coordinateDifferenceChart_apply,coordinateLeftDifference_self] using h

end DirectedCycles.GleasonLieAlgebra
