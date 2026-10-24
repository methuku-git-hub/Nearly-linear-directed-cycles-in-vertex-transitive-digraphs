import DirectedCycles.LocalExponentialCurveAnnulus
import DirectedCycles.NestedTangentScaleBounds

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
namespace LocalExponentialData
variable {H E : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ChartedSpace E H] {Q : LocalGroupAlgebra H} (D : LocalExponentialData (E := E) Q)

/-- Equality of actual exponential values identifies the signed tangent
when both coordinates lie within the constructed chart. -/
theorem coordinate_eq {v w : E} {t : ℝ} (hv : ‖v‖ < D.radius)
    (htw : |t| * ‖w‖ < D.radius) (he : D.chart v = D.chart (t • w)) : v = t • w := by
  apply D.chart.injOn
  · exact D.ball_source (by simpa only [Metric.mem_ball,dist_zero_right] using hv)
  · exact D.ball_source (by simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs] using htw)
  · exact he

/-- Nested annuli determine the signed scale of equal exponential endpoints.
The argument uses only the actual exponential chart, without global curves. -/
theorem signed_nested_scales {r δ t : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hR : (1001/1000)*r < D.radius) (ht : |t| ≤ 1)
    {v w : E} (he : D.chart v = D.chart (t • w))
    (hv : δ*r ≤ ‖v‖ ∧ ‖v‖ ≤ (1001/1000)*δ*r)
    (hw : r ≤ ‖w‖ ∧ ‖w‖ ≤ (1001/1000)*r) :
    v = t • w ∧ (99/100)*δ < |t| ∧ |t| < (101/100)*δ := by
  have hvR : ‖v‖ < D.radius := by
    have hh := mul_le_mul_of_nonneg_right hδ1 (show 0 ≤ (1001/1000)*r by positivity)
    nlinarith [hv.2]
  have htw : |t| * ‖w‖ < D.radius :=
    (mul_le_mul_of_nonneg_right ht (norm_nonneg w)).trans_lt
      (by simpa only [one_mul] using hw.2.trans_lt hR)
  have heq := D.coordinate_eq hvR htw he
  have hnorm : ‖v‖ = ‖|t| • w‖ := by simp only [heq,norm_smul,Real.norm_eq_abs,abs_abs]
  have hv' : δ*r ≤ ‖|t| • w‖ ∧ ‖|t| • w‖ ≤ (1001/1000)*δ*r := hnorm ▸ hv
  have hb := nested_tangent_scale_bounds (abs_nonneg t) (rfl : |t| • w = |t| • w) hr hv' hw
  have he₁ : δ*r/((1001/1000)*r) = (1000/1001)*δ := by field_simp
  have he₂ : ((1001/1000)*δ*r)/r = (1001/1000)*δ := by field_simp
  rw [he₁,he₂] at hb
  exact ⟨heq,by nlinarith [hb.1],by nlinarith [hb.2]⟩
end LocalExponentialData
end DirectedCycles
