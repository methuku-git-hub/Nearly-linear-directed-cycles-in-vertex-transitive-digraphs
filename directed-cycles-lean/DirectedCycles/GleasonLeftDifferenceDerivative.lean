import DirectedCycles.GleasonLeftDifferenceCoordinates
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
open Filter Topology Asymptotics
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The derivative of the actual left-difference coordinate map is the
proved averaged adjoint at every sufficiently small base point. -/
theorem coordinateLeftDifference_hasFDerivAt : ∃ δ : ℝ, 0 < δ ∧
    ∀ x : E, ‖x‖ < δ → HasFDerivAt (coordinateLeftDifference D e x)
      (coordinateAdjointAverage D e x) x := by
  obtain ⟨K,δ,hK,hδ,hbound⟩ := coordinateLeftDifference_quadratic_error D e
  refine ⟨δ,hδ,?_⟩
  intro x hx
  have hA := ((coordinateAdjointAverage_contDiff D e).differentiable (by norm_num)) x
  have hG : HasFDerivAt (fun y : E => coordinateAdjointAverage D e y (y-x))
      (coordinateAdjointAverage D e x) x := by
    have h := hA.hasFDerivAt.clm_apply ((hasFDerivAt_id x).sub_const x)
    simpa only [id_eq,sub_self,map_zero,add_zero,ContinuousLinearMap.comp_id] using h
  have hnear : ∀ᶠ h : E in 𝓝 0, ‖x+h‖ < δ := by
    have hc : ContinuousAt (fun h : E => ‖x+h‖) 0 := (continuous_const.add continuous_id).norm.continuousAt
    exact hc.eventually (gt_mem_nhds (by simpa only [add_zero] using hx))
  have hB : (fun h : E => coordinateLeftDifference D e x (x+h)-coordinateAdjointAverage D e (x+h) h)
      =O[𝓝 0] (fun h : E => ‖h‖^2) := by
    apply IsBigO.of_bound K
    filter_upwards [hnear] with h hh
    have hb := hbound x (x+h) hx.le hh.le
    simpa only [add_sub_cancel_left,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using hb
  have hR := hB.trans_isLittleO (isLittleO_norm_pow_id (E' := E) (by norm_num : 1 < 2))
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hG ⊢
  have hG' : (fun h : E => coordinateAdjointAverage D e (x+h) h-coordinateAdjointAverage D e x h)
      =o[𝓝 0] (fun h : E => h) := by
    simpa only [add_sub_cancel_left,sub_self,map_zero,sub_zero] using hG
  have hs := hR.add hG'
  have he : (fun h : E => (coordinateLeftDifference D e x (x+h)-coordinateAdjointAverage D e (x+h) h)+
      (coordinateAdjointAverage D e (x+h) h-coordinateAdjointAverage D e x h)) =
      (fun h : E => coordinateLeftDifference D e x (x+h)-coordinateLeftDifference D e x x-coordinateAdjointAverage D e x h) := by
    funext h
    rw [coordinateLeftDifference_self]
    abel
  rw [he] at hs
  exact hs

end DirectedCycles.GleasonLieAlgebra
