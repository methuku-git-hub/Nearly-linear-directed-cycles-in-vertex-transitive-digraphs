import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiating the genuine local multiplication identity transports a
curve's identity tangent to an autonomous differential equation nearby. -/
theorem local_curve_derivative_equation (μ : E × E → E)
    (hμ : ContDiffAt ℝ 1 μ (0,0)) (f : ℝ → E) (hf0 : f 0 = 0)
    {v : E} (hv : HasDerivAt f v 0) {r : ℝ} (hr : 0 < r)
    (hmul : ∀ s t : ℝ, |s|+|t| ≤ r → f (s+t) = μ (f s,f t)) :
    ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), HasDerivAt f ((fderiv ℝ μ (f t,0)) (0,v)) t := by
  have hd : ∀ᶠ p : E × E in 𝓝 (0,0), DifferentiableAt ℝ μ p :=
    (hμ.eventually (by simp)).mono (fun p hp => hp.differentiableAt one_ne_zero)
  have hc : ContinuousAt (fun t : ℝ => (f t,(0 : E))) 0 :=
    hv.continuousAt.prodMk continuousAt_const
  have hd' : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), DifferentiableAt ℝ μ (f t,0) :=
    (show Filter.Tendsto (fun t : ℝ => (f t,(0 : E))) (𝓝 0) (𝓝 (0,0)) by
      simpa only [ContinuousAt,hf0] using hc).eventually hd
  filter_upwards [hd',Metric.ball_mem_nhds (0 : ℝ) (show 0 < r/2 by positivity)] with t hdt ht
  have ht' : |t| < r/2 := by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht
  have hshift : HasDerivAt (fun s : ℝ => s-t) 1 t := (hasDerivAt_id t).sub_const t
  have hfv : HasDerivAt (fun s : ℝ => f (s-t)) v t := by
    have hh := hv.scomp_of_eq t hshift (sub_self t).symm
    simpa only [Function.comp_def,one_smul] using hh
  have hpair : HasDerivAt (fun s : ℝ => (f t,f (s-t))) (0,v) t :=
    (hasDerivAt_const t (f t)).prodMk hfv
  have hh := hdt.hasFDerivAt.comp_hasDerivAt_of_eq t hpair
    (show (f t,0) = (f t,f (t-t)) by rw [sub_self,hf0])
  apply hh.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds t (show 0 < r/2 by positivity)] with s hs
  have hs' : |s-t| < r/2 := by simpa only [Metric.mem_ball,Real.dist_eq] using hs
  simpa only [Function.comp_apply,add_sub_cancel] using hmul t (s-t) (by linarith)
end DirectedCycles
