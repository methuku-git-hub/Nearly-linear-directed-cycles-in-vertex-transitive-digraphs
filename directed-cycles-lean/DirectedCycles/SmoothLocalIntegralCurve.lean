module

public import DirectedCycles.AutonomousCurveSmoothness
public import DirectedCycles.LocalMultiplicationDerivative
public import Mathlib.Analysis.ODE.ExistUnique

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- An actual local integral curve of the left-invariant coordinate field
exists for every proposed tangent. This is an existence theorem, using
Picard--Lindelof, rather than an assumed exponential curve. -/
theorem exists_local_multiplication_integral_curve (μ : E × E → E)
    (hμ : ContDiffAt ℝ ∞ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id) (v : E) :
    ∃ f : ℝ → E, f 0 = 0 ∧ HasDerivAt f v 0 ∧ ContDiffAt ℝ ∞ f 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε →
        HasDerivAt f ((fderiv ℝ μ (f t,0)) (0,v)) t := by
  let V : E → E := fun x => (fderiv ℝ μ (x,0)) (0,v)
  have hD : ContDiffAt ℝ ∞ (fderiv ℝ μ) (0,0) := hμ.fderiv_right (by simp)
  have hpair : ContDiffAt ℝ ∞ (fun x : E => (x,(0 : E))) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hV : ContDiffAt ℝ ∞ V 0 :=
    (hD.comp (f := fun x : E => (x,(0 : E))) 0 hpair).clm_apply (contDiffAt_const (c := (0,v)))
  obtain ⟨f,hf0,ε,hε,hfder⟩ :=
    (hV.of_le (by simp) : ContDiffAt ℝ 1 V 0).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hder : ∀ t : ℝ, |t| < ε → HasDerivAt f (V (f t)) t := by
    intro t ht
    exact hfder t (by simpa only [zero_sub,zero_add,Set.mem_Ioo] using abs_lt.mp ht)
  have hderNear : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), HasDerivAt f (V (f t)) t := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
    exact hder t (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  have hV0 : V 0 = v := by
    have hd := fderiv_local_multiplication μ (hμ.differentiableAt (by simp)) hl hr
    change (fderiv ℝ μ (0,0)) (0,v) = v
    rw [hd]
    simp
  refine ⟨f,hf0,?_,contDiffAt_of_autonomous_derivative f V (by simpa only [hf0] using hV) hderNear,
    ε,hε,hder⟩
  simpa only [hf0,hV0] using hder 0 (by simpa only [abs_zero] using hε)
end DirectedCycles
