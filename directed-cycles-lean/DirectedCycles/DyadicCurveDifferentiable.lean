import DirectedCycles.DyadicLinearApproximation
import DirectedCycles.QuadraticCurveDerivative

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Dyadic contraction and quadratic local addition error force differentiability
of a continuous curve. Every approximation used here is constructed. -/
theorem hasDerivAt_of_dyadic_quadratic_addition (f : ℝ → E) (h0 : f 0 = 0)
    (hcont : ContinuousAt f 0) {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hc : ∀ t : ℝ, |t| ≤ r → ‖f (t/2)‖ ≤ (2/3)*‖f t‖)
    (ha : ∀ s t : ℝ, |s|+|t| ≤ r → ‖f (s+t)-f s-f t‖ ≤ C*(‖f s‖+‖f t‖)^2) :
    ∃ v : E, HasDerivAt f v 0 := by
  obtain ⟨v,hv⟩ := exists_dyadic_linear_approximation f h0 hcont hr hC hc ha
  refine ⟨v,hasDerivAt_of_curve_quadratic_error f v h0 hcont (by positivity : 0 ≤ 16*C) ?_⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr] with t ht
  have hh : |t| < r := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
  exact hv t hh.le
end DirectedCycles
