import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A quadratic approximation in the curve's own norm implies an ordinary
derivative, by first absorbing half that norm and obtaining a linear bound. -/
theorem hasDerivAt_of_curve_quadratic_error (f : ℝ → E) (v : E)
    (h0 : f 0 = 0) (hcont : ContinuousAt f 0) {K : ℝ} (hK : 0 ≤ K)
    (herr : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖f t-t • v‖ ≤ K*‖f t‖^2) : HasDerivAt f v 0 := by
  have hn : Filter.Tendsto (fun t => ‖f t‖) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [h0,norm_zero] using hcont.norm.tendsto
  have hkn : Filter.Tendsto (fun t => K*‖f t‖) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hn.const_mul K
  have hsmall : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), K*‖f t‖ < 1/2 :=
    hkn.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  have hlinear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖f t‖ ≤ 2*|t| *‖v‖ := by
    filter_upwards [herr,hsmall] with t he hs
    have hh := norm_add_le (f t-t • v) (t • v)
    rw [sub_add_cancel,norm_smul,Real.norm_eq_abs] at hh
    have hs' := mul_le_mul_of_nonneg_right hs.le (norm_nonneg (f t))
    nlinarith
  let B : ℝ := 4*K*‖v‖^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hquadratic : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ‖f t-t • v‖ ≤ B*|t|^2 := by
    filter_upwards [herr,hlinear] with t he hl
    have hs := pow_le_pow_left₀ (norm_nonneg (f t)) hl 2
    have hh := he.trans (mul_le_mul_of_nonneg_left hs hK)
    convert hh using 1
    dsimp [B]
    ring
  rw [hasDerivAt_iff_isLittleO]
  simp only [h0,sub_zero]
  apply Asymptotics.isLittleO_iff.2
  intro ε hε
  have heps : 0 < ε/(B+1) := div_pos hε (by linarith)
  have hnear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| < ε/(B+1) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) heps] with t ht
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
  filter_upwards [hquadratic,hnear] with t hq ht
  have hmul := (lt_div_iff₀ (by linarith : 0 < B+1)).1 ht
  have hbe : B*|t| ≤ ε := by nlinarith [abs_nonneg t]
  have hh := mul_le_mul_of_nonneg_right hbe (abs_nonneg t)
  simpa only [Real.norm_eq_abs] using hq.trans (by nlinarith)
end DirectedCycles
