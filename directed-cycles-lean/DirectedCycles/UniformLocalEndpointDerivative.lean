module

public import DirectedCycles.ParameterIntegralEndpointDerivative
public import DirectedCycles.UniformLocalOneParameterExistence

@[expose] public section

set_option autoImplicit false
open scoped Topology ContDiff
namespace DirectedCycles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Local multiplication curves can be constructed on common intervals with
strictly differentiable endpoint maps. All existence, parameter bounds and
multiplication identities are proved from the actual smooth local product. -/
theorem exists_uniform_local_endpoint_derivative (μ : E × E → E)
    (hμ : ContDiffAt ℝ ∞ μ (0,0))
    (hl : (fun x => μ (x,0)) =ᶠ[𝓝 (0 : E)] id)
    (hr : (fun x => μ (0,x)) =ᶠ[𝓝 (0 : E)] id)
    (hassoc : ∀ᶠ p : E × E in 𝓝 (0,0),
      (fun z => μ (μ (p.1,p.2),z)) =ᶠ[𝓝 (0 : E)] (fun z => μ (p.1,μ (p.2,z)))) :
    ∃ f : E × ℝ → E, ContinuousAt f (0,0) ∧
      (∀ᶠ v : E in 𝓝 0, f (v,0) = 0 ∧ HasDerivAt (fun t => f (v,t)) v 0) ∧
      ∃ R r ε : ℝ, 0 < R ∧ 0 < r ∧ 0 < ε ∧
        (∀ v : E, ‖v‖ < R → ∀ s t : ℝ, |s|+|t| ≤ r → f (v,s+t) = μ (f (v,s),f (v,t))) ∧
        (∀ t : ℝ, |t| < ε → f (0,t) = 0) ∧
        (∀ τ : ℝ, 0 < τ → τ < ε →
          HasStrictFDerivAt (fun v => f (v,τ)) (τ • ContinuousLinearMap.id ℝ E) 0) := by
  let A : E → E →L[ℝ] E := fun x => (fderiv ℝ μ (x,0)).comp (ContinuousLinearMap.inr ℝ E E)
  have hD : ContDiffAt ℝ 1 (fderiv ℝ μ) (0,0) :=
    (hμ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by simp)).fderiv_right (by norm_num)
  have hpair : ContDiffAt ℝ 1 (fun x : E => (x,(0 : E))) 0 := contDiffAt_id.prodMk contDiffAt_const
  have hA : ContDiffAt ℝ 1 A 0 :=
    (hD.comp (f := fun x : E => (x,(0 : E))) 0 hpair).clm_comp contDiffAt_const
  have hA0 : A 0 = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    exact (fderiv_local_multiplication μ (hμ.differentiableAt (by simp)) hl hr (0,v)).trans (zero_add v)
  obtain ⟨a,ε,ha,hε,K,f,hder,hLip,hcont⟩ := exists_lipschitz_parameter_integral_curves A hA
  have hfc : ContinuousAt f (0,0) := by
    apply hcont.continuousAt
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Metric.closedBall_mem_nhds (0 : E) ha) (Icc_mem_nhds (by linarith) (by linarith))
  have hfinit : ∀ᶠ v : E in 𝓝 0, f (v,0) = 0 ∧ HasDerivAt (fun t => f (v,t)) v 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) ha] with v hv
    have hv' : ‖v‖ ≤ a := le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hv)
    refine ⟨(hder v hv').1,?_⟩
    simpa only [(hder v hv').1,hA0,ContinuousLinearMap.id_apply] using
      (hder v hv').2 0 (by simpa only [abs_zero] using hε)
  have hderNear : ∀ᶠ p : E × ℝ in 𝓝 (0,0), HasDerivAt (fun t => f (p.1,t)) (A (f p) p.1) p.2 := by
    have hfst : Filter.Tendsto (fun p : E × ℝ => p.1) (𝓝 (0,0)) (𝓝 0) := continuousAt_fst
    have hsnd : Filter.Tendsto (fun p : E × ℝ => p.2) (𝓝 (0,0)) (𝓝 0) := continuousAt_snd
    filter_upwards [hfst.eventually (Metric.ball_mem_nhds (0 : E) ha),hsnd.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)] with p hp ht
    exact (hder p.1 (le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hp))).2 p.2
      (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  obtain ⟨J,S,hS,hALip⟩ := exists_uniform_operator_field_lipschitz A hA
  have hALipNear : ∀ᶠ v : E in 𝓝 0, LipschitzOnWith J (fun x => A x v) S := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with v hv
    exact hALip v (le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hv))
  obtain ⟨R,r,hR,hr',hlaw⟩ := uniform_integral_curve_multiplication μ (fun v x => A x v)
    (hμ.of_le (by simp)) hl (local_multiplication_invariant_field_all μ (hμ.of_le (by simp)) hl hassoc)
    S hS J hALipNear f hfc (hfinit.mono fun _ h => h.1) hderNear
  exact ⟨f,hfc,hfinit,R,r,ε,hR,hr',hε,hlaw,
    (parameter_integral_curve_norm_bound A f ha.le hε K hder hLip).1,
    fun τ hτ hτε => parameter_integral_endpoint_strict_derivative A hA hA0 f ha hε K hder hLip hτ hτε⟩
end DirectedCycles
