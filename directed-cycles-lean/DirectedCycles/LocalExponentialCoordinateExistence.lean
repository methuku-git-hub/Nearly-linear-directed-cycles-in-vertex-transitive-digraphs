module

public import DirectedCycles.UniformLocalEndpointDerivative
public import DirectedCycles.UniformLocalCurveScaling
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Smooth local multiplication has actual exponential coordinates with a
strict identity derivative and the exact radial law. The coordinates are
constructed from uniformly controlled ODE solutions and their proved scaling. -/
theorem exists_local_exponential_coordinate_map (μ : E × E → E)
    (hμ : ContDiffAt ℝ ∞ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (hassoc : ∀ᶠ p : E × E in 𝓝 (0,0),
      (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z)))) :
    ∃ F : E → E, F 0 = 0 ∧ HasStrictFDerivAt F (ContinuousLinearMap.id ℝ E) 0 ∧
      ∃ R : ℝ, 0 < R ∧ ∀ v : E, ‖v‖ < R → ∀ s t : ℝ, |s|+|t| ≤ 1 →
        F ((s+t) • v) = μ (F (s • v),F (t • v)) := by
  obtain ⟨f,_,hfinit,R,r,ε,hR,hr0,hε,hflaw,hfzero,hstrict⟩ :=
    exists_uniform_local_endpoint_derivative μ hμ hl hr hassoc
  obtain ⟨η,hη,hηinit⟩ := Metric.mem_nhds_iff.mp hfinit
  let ρ := min R η
  have hρ : 0 < ρ := lt_min hR hη
  have hinit : ∀ v : E, ‖v‖ < ρ → f (v,0) = 0 ∧ HasDerivAt (fun t => f (v,t)) v 0 := by
    intro v hv
    apply hηinit
    simpa only [Metric.mem_ball,dist_zero_right] using hv.trans_le (min_le_right _ _)
  have hlaw : ∀ v : E, ‖v‖ < ρ → ∀ s t : ℝ, |s|+|t| ≤ r →
      f (v,s+t) = μ (f (v,s),f (v,t)) :=
    fun v hv => hflaw v (hv.trans_le (min_le_left _ _))
  let τ := min ε r/2
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτε : τ < ε := by have := min_le_left ε r; dsimp only [τ]; linarith
  have hτr : τ ≤ r := by have := min_le_right ε r; dsimp only [τ]; linarith
  let F : E → E := fun v => f (τ⁻¹ • v,τ)
  have hF0 : F 0 = 0 := by
    dsimp only [F]
    rw [smul_zero]
    exact hfzero τ (by rwa [abs_of_pos hτ])
  have hlin : HasStrictFDerivAt (fun v : E => τ⁻¹ • v) (τ⁻¹ • ContinuousLinearMap.id ℝ E) 0 :=
    (τ⁻¹ • ContinuousLinearMap.id ℝ E).hasStrictFDerivAt
  have he : HasStrictFDerivAt (fun v => f (v,τ)) (τ • ContinuousLinearMap.id ℝ E)
      (τ⁻¹ • (0 : E)) := by simpa only [smul_zero] using hstrict τ hτ hτε
  have hD : HasStrictFDerivAt F (ContinuousLinearMap.id ℝ E) 0 := by
    have hd := he.comp (f := fun v : E => τ⁻¹ • v) 0 hlin
    have hlinear : (τ • ContinuousLinearMap.id ℝ E).comp (τ⁻¹ • ContinuousLinearMap.id ℝ E) =
        ContinuousLinearMap.id ℝ E := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,
        smul_smul,mul_inv_cancel₀ hτ.ne',one_smul]
    simpa only [hlinear,Function.comp_def,F] using hd
  refine ⟨F,hF0,hD,τ*ρ,mul_pos hτ hρ,?_⟩
  intro v hv s t hst
  have hvρ : ‖τ⁻¹ • v‖ < ρ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hτ),inv_mul_eq_div]
    exact (div_lt_iff₀ hτ).2 (by simpa only [mul_comm] using hv)
  have hscale : ∀ a : ℝ, |a| ≤ 1 → F (a • v) = f (τ⁻¹ • v,a*τ) := by
    intro a ha
    have heq := uniform_local_curve_scaling μ (hμ.of_le (by simp)) f hr0 hinit hlaw
      (τ⁻¹ • v) hvρ a ha τ (by rw [abs_of_pos hτ]; exact hτr)
    simpa only [F,smul_smul,mul_comm τ⁻¹ a] using heq
  have hs : |s| ≤ 1 := by linarith [abs_nonneg t]
  have ht : |t| ≤ 1 := by linarith [abs_nonneg s]
  have hsum : |s+t| ≤ 1 := (abs_add_le s t).trans hst
  rw [hscale (s+t) hsum,hscale s hs,hscale t ht,add_mul]
  apply hlaw _ hvρ
  rw [abs_mul,abs_mul,abs_of_pos hτ,← add_mul]
  exact (mul_le_mul_of_nonneg_right hst hτ.le).trans (by simpa only [one_mul] using hτr)
end DirectedCycles
