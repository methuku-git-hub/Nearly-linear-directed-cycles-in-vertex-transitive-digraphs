module

public import DirectedCycles.SmoothParameterIntegralCurves
public import DirectedCycles.UniformIntegralCurveMultiplication
public import DirectedCycles.UniformOperatorFieldLipschitz
public import DirectedCycles.LocalInvariantOperatorField

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual local one-parameter curves can be chosen jointly continuously with
a common multiplication interval for all sufficiently small tangents. -/
theorem exists_uniform_local_one_parameter_curves (μ : E × E → E)
    (hμ : ContDiffAt ℝ ∞ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (hassoc : ∀ᶠ p : E × E in 𝓝 (0,0),
      (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z)))) :
    ∃ f : E × ℝ → E, ContinuousAt f (0,0) ∧
      (∃ D : Set (E × ℝ), IsOpen D ∧ (0,0) ∈ D ∧ ContinuousOn f D) ∧
      (∀ᶠ v : E in 𝓝 0, f (v,0) = 0 ∧ HasDerivAt (fun t => f (v,t)) v 0) ∧
      ∃ R r : ℝ, 0 < R ∧ 0 < r ∧ ∀ v : E, ‖v‖ < R →
        ∀ s t : ℝ, |s|+|t| ≤ r → f (v,s+t) = μ (f (v,s),f (v,t)) := by
  let A : E → E →L[ℝ] E := fun x => (fderiv ℝ μ (x,0)).comp (ContinuousLinearMap.inr ℝ E E)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ μ) (0,0) :=
    (hμ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by simp)).fderiv_right (by norm_num)
  have hpair : ContDiffAt ℝ 1 (fun x : E => (x,(0 : E))) 0 := contDiffAt_id.prodMk contDiffAt_const
  have hA : ContDiffAt ℝ 1 A 0 :=
    (hD.comp (f := fun x : E => (x,(0 : E))) 0 hpair).clm_comp contDiffAt_const
  obtain ⟨f,hfc,hcontOn,hf0,hder⟩ := exists_continuous_parameter_integral_curves A hA
  have hA0 : ∀ v : E, A 0 v = v := by
    intro v
    exact (fderiv_local_multiplication μ (hμ.differentiableAt (by simp)) hl hr (0,v)).trans (zero_add v)
  obtain ⟨K,S,hS,hLip⟩ := exists_uniform_operator_field_lipschitz A hA
  have hLipNear : ∀ᶠ v : E in 𝓝 0, LipschitzOnWith K (fun x => A x v) S := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with v hv
    exact hLip v (le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hv))
  have hder0 : ∀ᶠ v : E in 𝓝 0, HasDerivAt (fun t => f (v,t)) (A (f (v,0)) v) 0 :=
    (continuousAt_id.prodMk continuousAt_const).eventually hder
  have hfInit : ∀ᶠ v : E in 𝓝 0, f (v,0) = 0 ∧ HasDerivAt (fun t => f (v,t)) v 0 := by
    filter_upwards [hf0,hder0] with v h0 hd
    exact ⟨h0,by simpa only [h0,hA0] using hd⟩
  exact ⟨f,hfc,hcontOn,hfInit,uniform_integral_curve_multiplication μ (fun v x => A x v)
    (hμ.of_le (by simp)) hl (local_multiplication_invariant_field_all μ (hμ.of_le (by simp)) hl hassoc)
    S hS K hLipNear f hfc hf0 hder⟩
end DirectedCycles
