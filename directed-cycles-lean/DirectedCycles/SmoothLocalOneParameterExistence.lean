import DirectedCycles.SmoothLocalIntegralCurve
import DirectedCycles.LocalMultiplicationInvariantField
import DirectedCycles.LocalIntegralCurveMultiplication

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Smooth locally associative multiplication has an actual local
one-parameter curve with every prescribed tangent. Existence comes from an
ODE, and the multiplication identity is proved by uniqueness. -/
theorem exists_smooth_local_one_parameter_curve (μ : E × E → E)
    (hμ : ContDiffAt ℝ ∞ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (hassoc : ∀ᶠ p : E × E in 𝓝 (0,0),
      (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z)))) (v : E) :
    ∃ f : ℝ → E, f 0 = 0 ∧ HasDerivAt f v 0 ∧ ContDiffAt ℝ ∞ f 0 ∧
      ∃ r : ℝ, 0 < r ∧ ∀ s t : ℝ, |s|+|t| ≤ r → f (s+t) = μ (f s,f t) := by
  obtain ⟨f,hf0,hfv,hfSmooth,ε,hε,hder⟩ := exists_local_multiplication_integral_curve μ hμ hl hr v
  let V : E → E := fun x => (fderiv ℝ μ (x,0)) (0,v)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ μ) (0,0) := (hμ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by simp)).fderiv_right (by norm_num)
  have hpair : ContDiffAt ℝ 1 (fun x : E => (x,(0 : E))) 0 := contDiffAt_id.prodMk contDiffAt_const
  have hV : ContDiffAt ℝ 1 V 0 :=
    (hD.comp (f := fun x : E => (x,(0 : E))) 0 hpair).clm_apply (contDiffAt_const (c := (0,v)))
  have hderNear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), HasDerivAt f (V (f t)) t := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    exact hder t (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  exact ⟨f,hf0,hfv,hfSmooth,local_integral_curve_multiplication μ V (hμ.of_le (by simp)) hV hl
    (local_multiplication_invariant_field μ (hμ.of_le (by simp)) hl hassoc v) f hf0 hderNear⟩
end DirectedCycles
