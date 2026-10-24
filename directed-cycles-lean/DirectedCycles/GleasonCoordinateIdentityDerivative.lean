import DirectedCycles.GleasonCoordinateQuadratic
import Mathlib.Analysis.Asymptotics.Lemmas

set_option autoImplicit false
open Filter Topology Asymptotics
open scoped Topology
namespace DirectedCycles.GleasonLieAlgebra
variable {G E : Type*} [Group G] [TopologicalSpace G]
    (D : GleasonMetricData G) [IsTopologicalGroup G] [LocallyCompactSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : GleasonLieAlgebra D ≃L[ℝ] E)

/-- The constructed local multiplication has derivative addition at the
identity pair, as a consequence of its proved quadratic error estimate. -/
theorem coordinateMul_hasFDerivAt_zero : HasFDerivAt (coordinateMul D e)
    (ContinuousLinearMap.fst ℝ E E+ContinuousLinearMap.snd ℝ E E) (0,0) := by
  obtain ⟨K,r,hK,hr,hbound⟩ := coordinateMul_quadratic_error D e
  have hB : (fun p : E × E => coordinateMul D e p-p.1-p.2) =O[𝓝 (0 : E × E)]
      (fun p => ‖p‖^2) := by
    apply IsBigO.of_bound K
    filter_upwards [Metric.ball_mem_nhds (0 : E × E) hr] with p hp
    have hpn : ‖p‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hp
    have hfst : ‖p.1‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have hsnd : ‖p.2‖ ≤ ‖p‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    have h := hbound p.1 p.2 (hfst.trans_lt hpn) (hsnd.trans_lt hpn)
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖p‖)]
    have hm := mul_le_mul hfst hsnd (norm_nonneg p.2) (norm_nonneg p)
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hm hK.le])
  have hL := hB.trans_isLittleO (isLittleO_norm_pow_id (E' := E × E) (by norm_num : 1 < 2))
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  change (fun h : E × E => coordinateMul D e (0+h)-coordinateMul D e (0,0)-(h.1+h.2)) =o[𝓝 0] (fun h => h)
  simpa only [zero_add,coordinateMul_zero,sub_zero,sub_add_eq_sub_sub] using hL

end DirectedCycles.GleasonLieAlgebra
