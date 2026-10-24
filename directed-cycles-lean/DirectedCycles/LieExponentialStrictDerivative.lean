import DirectedCycles.UniformLocalEndpointDerivative
import DirectedCycles.LieCoordinateCurveRealization
import DirectedCycles.LieIdentityCoordinateMultiplication

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- The constructed Lie exponential has strict derivative the identity in
actual identity-chart coordinates. The two-point estimate is derived from the
parameter ODE, not inferred from derivatives on individual lines. -/
theorem lie_exponential_coordinate_strict_derivative :
    HasStrictFDerivAt (fun v : E => (chartAt E (1 : G)) (lieExponential v)-(chartAt E (1 : G)) 1)
      (ContinuousLinearMap.id ℝ E) 0 := by
  let e := chartAt E (1 : G)
  let c : E := e 1
  let chart : G → E := fun x => e x-c
  let unchart : E → G := fun y => e.symm (y+c)
  let μ : E × E → E := fun p => chart (unchart p.1*unchart p.2)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : c ∈ e.target := e.mapsTo h1
  have hright : (fun x => chart (unchart x)) =ᶠ[𝓝 (0 : E)] id := by
    have hcont : ContinuousAt (fun x : E => x+c) 0 := continuousAt_id.add continuousAt_const
    have htarget : ∀ᶠ x in 𝓝 (0 : E), x+c ∈ e.target :=
      hcont.preimage_mem_nhds (by simpa only [zero_add] using e.open_target.mem_nhds hc)
    filter_upwards [htarget] with x hx
    dsimp only [chart,unchart,id]
    rw [e.right_inv hx,add_sub_cancel_right]
  obtain ⟨hμ,hl,hr,hassoc⟩ := lie_group_identity_coordinate_multiplication (G := G) (E := E)
  obtain ⟨f,hfc,hfinit,R,r,ε,hR,hr0,hε,hflaw,hfzero,hstrict⟩ :=
    exists_uniform_local_endpoint_derivative μ hμ hl hr hassoc
  obtain ⟨R',r',hR',hr',hreal⟩ := lie_coordinate_curve_family_realization (G := G) f hfc hfinit hR hr0 hflaw
  let τ := min ε r'/2
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hτε : τ < ε := by have := min_le_left ε r'; dsimp only [τ]; linarith
  have hτr : τ ≤ r' := by have := min_le_right ε r'; have := lt_min hε hr'; dsimp only [τ]; linarith
  have hτabs : |τ| < ε := by rwa [abs_of_pos hτ]
  have hfτ : Filter.Tendsto (fun v => f (v,τ)) (𝓝 0) (𝓝 (0 : E)) := by
    simpa only [hfzero τ hτabs] using (hstrict τ hτ hτε).continuousAt.tendsto
  have heq : (fun v => chart (lieExponential (G := G) (τ • v))) =ᶠ[𝓝 (0 : E)] (fun v => f (v,τ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) hR',hfτ.eventually hright] with v hv he
    have hvR : ‖v‖ < R' := by simpa only [Metric.mem_ball,dist_zero_right] using hv
    have hreal' := hreal v hvR τ (by rw [abs_of_pos hτ]; exact hτr)
    change unchart (f (v,τ)) = lieExponential (G := G) (τ • v) at hreal'
    rw [← hreal']
    exact he
  have hqd : HasStrictFDerivAt (fun v => chart (lieExponential (G := G) (τ • v)))
      (τ • ContinuousLinearMap.id ℝ E) 0 := (hstrict τ hτ hτε).congr_of_eventuallyEq heq.symm
  have hlin : HasStrictFDerivAt (fun v : E => τ⁻¹ • v) (τ⁻¹ • ContinuousLinearMap.id ℝ E) 0 :=
    (τ⁻¹ • ContinuousLinearMap.id ℝ E).hasStrictFDerivAt
  have hqd' : HasStrictFDerivAt (fun v => chart (lieExponential (G := G) (τ • v)))
      (τ • ContinuousLinearMap.id ℝ E) (τ⁻¹ • (0 : E)) := by simpa only [smul_zero] using hqd
  have hd := hqd'.comp (f := fun v : E => τ⁻¹ • v) 0 hlin
  have hlinear : (τ • ContinuousLinearMap.id ℝ E).comp (τ⁻¹ • ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,
      smul_smul,mul_inv_cancel₀ hτ.ne',one_smul]
  rw [hlinear] at hd
  simpa only [Function.comp_def,smul_smul,mul_inv_cancel₀ hτ.ne',one_smul] using hd
end DirectedCycles
