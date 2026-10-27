module

public import DirectedCycles.LieIdentityCoordinateMultiplication
public import DirectedCycles.SmoothLocalOneParameterExistence
public import DirectedCycles.LocalCurveExtension
public import DirectedCycles.LieOneParameterSmooth

@[expose] public section

set_option autoImplicit false
open scoped Topology Manifold ContDiff
namespace DirectedCycles
variable {G E : Type*} [Group G] [TopologicalSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [ChartedSpace E G]
    [hLie : LieGroup 𝓘(ℝ,E) ∞ G]

include hLie in
/-- Every identity-coordinate tangent of a smooth real Lie group is realized
by an actual global smooth one-parameter subgroup. The curve is constructed
from a local ODE and then extended by finite subdivisions. -/
theorem lie_group_exists_one_parameter (v : E) :
    ∃ φ : ℝ → G, φ 0 = 1 ∧ (∀ s t : ℝ, φ (s+t) = φ s*φ t) ∧
      ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ φ ∧
      HasDerivAt (fun t => (chartAt E (1 : G)) (φ t)-(chartAt E (1 : G)) 1) v 0 := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := 𝓘(ℝ,E)) (n := ∞)
  let e := chartAt E (1 : G)
  let c : E := e 1
  let chart : G → E := fun x => e x-c
  let unchart : E → G := fun y => e.symm (y+c)
  let μ : E × E → E := fun p => chart (unchart p.1*unchart p.2)
  have h1 : (1 : G) ∈ e.source := mem_chart_source E 1
  have hc : c ∈ e.target := e.mapsTo h1
  have hu0 : unchart 0 = 1 := by
    dsimp only [unchart]
    rw [zero_add]
    exact e.left_inv h1
  have hleft : ∀ x ∈ e.source, unchart (chart x) = x := by
    intro x hx
    dsimp only [unchart,chart]
    rw [sub_add_cancel]
    exact e.left_inv hx
  have huCont : ContinuousAt unchart (0 : E) := by
    have he : ContinuousAt e.symm ((0 : E)+c) := by simpa only [zero_add] using e.symm.continuousAt hc
    exact he.comp (f := fun y : E => y+c) (continuousAt_id.add continuousAt_const)
  have hright : (fun x => chart (unchart x)) =ᶠ[𝓝 (0 : E)] id := by
    have hcont : ContinuousAt (fun x : E => x+c) 0 := continuousAt_id.add continuousAt_const
    have htarget : ∀ᶠ x in 𝓝 (0 : E), x+c ∈ e.target :=
      hcont.preimage_mem_nhds (by simpa only [zero_add] using e.open_target.mem_nhds hc)
    filter_upwards [htarget] with x hx
    dsimp only [chart,unchart,id]
    rw [e.right_inv hx,add_sub_cancel_right]
  obtain ⟨hμ,hl,hr,hassoc⟩ := lie_group_identity_coordinate_multiplication (G := G) (E := E)
  obtain ⟨f,hf0,hfv,_,r,hr0,hfadd⟩ := exists_smooth_local_one_parameter_curve μ hμ hl hr hassoc v
  let γ : ℝ → G := fun t => unchart (f t)
  have hγ0 : γ 0 = 1 := by dsimp only [γ]; rw [hf0,hu0]
  have hγc : ContinuousAt γ 0 := by
    have hu : ContinuousAt unchart (f 0) := by simpa only [hf0] using huCont
    exact hu.comp hfv.continuousAt
  have hγT : Filter.Tendsto γ (𝓝 0) (𝓝 (1 : G)) := by simpa only [hγ0] using hγc.tendsto
  have hfst : Filter.Tendsto (fun p : ℝ × ℝ => p.1) (𝓝 (0,0)) (𝓝 0) := continuousAt_fst
  have hsnd : Filter.Tendsto (fun p : ℝ × ℝ => p.2) (𝓝 (0,0)) (𝓝 0) := continuousAt_snd
  have hprodT : Filter.Tendsto (fun p : ℝ × ℝ => γ p.1*γ p.2) (𝓝 (0,0)) (𝓝 (1 : G)) := by
    simpa only [one_mul,Function.comp_def] using (hγT.comp hfst).mul (hγT.comp hsnd)
  have hprod : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), γ p.1*γ p.2 ∈ e.source :=
    hprodT.eventually (e.open_source.mem_nhds h1)
  obtain ⟨δ,hδ,hδprod⟩ := Metric.mem_nhds_iff.mp hprod
  let ρ := min r (δ/2)
  have hρ : 0 < ρ := lt_min hr0 (by positivity)
  have hγadd : ∀ s t : ℝ, |s|+|t| ≤ ρ → γ (s+t) = γ s*γ t := by
    intro s t hst
    have hs : |s| < δ := by have := min_le_right r (δ/2); linarith [abs_nonneg t]
    have ht : |t| < δ := by have := min_le_right r (δ/2); linarith [abs_nonneg s]
    have hstSource : γ s*γ t ∈ e.source := hδprod (show (s,t) ∈ Metric.ball (0,0) δ from by
      simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,sub_zero] using max_lt hs ht)
    change unchart (f (s+t)) = γ s*γ t
    rw [hfadd s t (hst.trans (min_le_left _ _))]
    exact hleft _ hstSource
  obtain ⟨φ,hφ0,hφadd,hagree⟩ := exists_local_curve_extension γ hγ0 hρ hγadd
  have heq : φ =ᶠ[𝓝 (0 : ℝ)] γ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with t ht
    exact hagree t (le_of_lt (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht))
  have hφc : ContinuousAt φ 0 := hγc.congr_of_eventuallyEq heq
  have hfT : Filter.Tendsto f (𝓝 0) (𝓝 (0 : E)) := by simpa only [hf0] using hfv.continuousAt.tendsto
  have hcoordEq : (fun t => chart (φ t)) =ᶠ[𝓝 (0 : ℝ)] f := by
    filter_upwards [heq,hfT.eventually hright] with t ht hf
    rw [ht]
    exact hf
  exact ⟨φ,hφ0,hφadd,lieGroup_one_parameter_contMDiff (E := E) φ hφ0 hφc hφadd,
    hfv.congr_of_eventuallyEq hcoordEq⟩
end DirectedCycles
