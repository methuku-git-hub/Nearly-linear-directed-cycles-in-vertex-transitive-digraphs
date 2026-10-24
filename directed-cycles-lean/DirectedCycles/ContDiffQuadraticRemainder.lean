import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A twice continuously differentiable map has an actual quadratic first-order
remainder in a neighbourhood of zero. -/
theorem contDiffAt_quadratic_remainder (f : E → F) (hf : ContDiffAt ℝ 2 f 0) :
    ∃ K r : ℝ, 0 ≤ K ∧ 0 < r ∧ ∀ x : E, ‖x‖ < r →
      ‖f x-f 0-(fderiv ℝ f 0) x‖ ≤ K*‖x‖^2 := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ f) 0 := hf.fderiv_right (by norm_num)
  obtain ⟨K,U,hU,hLip⟩ := hD.exists_lipschitzOnWith
  have hdiff : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℝ f x :=
    (hf.eventually (by norm_num)).mono (fun x hx => hx.differentiableAt (by norm_num))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU hdiff)
  refine ⟨K,r,K.coe_nonneg,hr,?_⟩
  intro x hx
  have h0 : (0 : E) ∈ Metric.ball 0 r := Metric.mem_ball_self hr
  have hzero : (0 : E) ∈ U := (hball h0).1
  have hsub : Metric.closedBall (0 : E) ‖x‖ ⊆ Metric.ball 0 r := by
    intro y hy
    simp only [Metric.mem_closedBall,Metric.mem_ball,dist_zero_right] at hy ⊢
    exact hy.trans_lt hx
  have hbound : ∀ y ∈ Metric.closedBall (0 : E) ‖x‖,
      ‖fderiv ℝ f y-fderiv ℝ f 0‖ ≤ (K : ℝ)*‖x‖ := by
    intro y hy
    have hb := hLip.dist_le_mul y (hball (hsub hy)).1 0 hzero
    rw [dist_eq_norm,dist_zero_right] at hb
    have hy' : ‖y‖ ≤ ‖x‖ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hy
    exact hb.trans (mul_le_mul_of_nonneg_left hy' K.coe_nonneg)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le'
    (fun y hy => (hball (hsub hy)).2) hbound (convex_closedBall (0 : E) ‖x‖)
    (Metric.mem_closedBall_self (norm_nonneg x))
    (show x ∈ Metric.closedBall (0 : E) ‖x‖ by simp)
  simpa only [sub_zero,mul_assoc,pow_two] using hh
end DirectedCycles
